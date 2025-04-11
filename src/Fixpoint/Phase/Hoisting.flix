mod Fixpoint.Phase.Hoisting {
    use MutDisjointSets.MutDisjointSets
    use Fixpoint.Ast.Ram.{RamStmt, RelOp, RelSym, RamTerm, BoolExp, RowVar, RamProgram, RamId}
    use Fixpoint.Ast.Ram.RelOp.{Search, Query, Functional, Project, If}
    use Fixpoint.Ast.Ram.BoolExp.{IsEmpty, NotMemberOf, Eq, Guard0, Guard1, Guard2, Guard3, Guard4, Guard5}
    use Fixpoint.Ast.Ram.RamTerm.{Lit, RowLoad, Meet, App0, App1, App2, App3, App4, App5}
    use Fixpoint.Boxed

    type alias Load = (RowVar, Int32)

    // Hoist if-constructions as far as possible and merge into Query when possible/relevant.
    // TODO: We could use a disjoin set datastructure to move up and minimize the number of equalities needed
    @Internal
    pub def hoistProgram(program: RamProgram): RamProgram = match program { 
        case RamProgram.Program(stmt, facts, meta, index) => region rc {
            let equalitySets = MutDisjointSets.empty(rc);
            let constEqualities = MutMap.empty(rc);
            unifyEqualitiesStmt(equalitySets, constEqualities, stmt);
            let termMap = MutMap.empty(rc);
            let impossible = MutSet.empty(rc);
            MutMap.forEach(load -> listOfPairs -> List.forEach(match (val, id) -> {
                let rep = unwrap(MutDisjointSets.find(load, equalitySets));
                match MutMap.get(rep, termMap) {
                    case Some(RamTerm.Lit(v, _)) => 
                        if(v != val) MutSet.add(fst(rep), impossible)
                        else ()
                    case Some(_) => bug!("In Hoisting.hoistStmt: termMap contains non-literals!")
                    case None => MutMap.put(rep, RamTerm.Lit(val, id), termMap)
                }
            }, listOfPairs), constEqualities);
            match hoistStmt(rc, termMap, equalitySets, impossible, stmt) {
                case None => RamProgram.Program(RamStmt.Comment("No rules are satisfiable"), facts, meta, index)
                case Some(hoistedStmt) => RamProgram.Program(hoistedStmt, facts, meta, index)
            }
        }
    }

    @Internal
    pub def hoistStmt(
        rc: Region[r],
        termMap: MutMap[Load, RamTerm, r],
        equalitySets: MutDisjointSets[Load, r], 
        impossible: MutSet[RowVar, r], 
        stmt: RamStmt
    ): Option[RamStmt] \ r = match stmt {
        case RamStmt.Insert(op) =>
            let independent = MutList.empty(rc);
            let optNewOp = hoistOp(rc, termMap, equalitySets, impossible, MutMap.empty(rc), independent, op);
            match optNewOp {
                case None => None 
                case Some(newOp) => 
                    if (MutList.size(independent) == 0) 
                        Some(RamStmt.Insert(newOp)) 
                    else Some(RamStmt.Insert(If(MutList.toVector(independent), newOp)))

            }
        case RamStmt.Seq(xs) =>
            let children =
                Vector.filterMap(hoistStmt(rc, termMap, equalitySets, impossible), xs);
            if (Vector.isEmpty(children)) None
            else if (Vector.length(children) == 1)
                Vector.head(children)
            else Some(RamStmt.Seq(children))
        case RamStmt.Par(xs) => 
            let children =
                Vector.filterMap(hoistStmt(rc, termMap, equalitySets, impossible), xs);
            if (Vector.isEmpty(children)) None
            else if (Vector.length(children) == 1)
                Vector.head(children)
            else Some(RamStmt.Par(children))
        case RamStmt.Until(test, body) =>
            match hoistStmt(rc, termMap, equalitySets, impossible, body) {
                case None => None
                case Some(v) => Some(RamStmt.Until(test, v))
            }
            // ???
            // RamStmt.Until(test, hoistStmt(termMap, equalitySets, impossible, body))
        case RamStmt.Merge(_, _) => Some(stmt)
        case RamStmt.Swap(_, _) => Some(stmt)
        case RamStmt.Purge(_) => Some(stmt)
        case RamStmt.Comment(_) => Some(stmt)
    }

    /// Takes the relative operator, op, region rc, and tuple-vars defined so far, seenRowVars 
    /// Rewrites the relative operator, op, as the first return value, and a map from tuple-vars to 
    @Internal
    def hoistOp(
        rc: Region[r],
        termMap: MutMap[Load, RamTerm, r],
        equalitySets: MutDisjointSets[Load, r], 
        impossible: MutSet[RowVar, r], 
        idToBool: MutMap[Int32, MutList[BoolExp, r], r],
        independentBool: MutList[BoolExp, r],
        op: RelOp
    ): Option[RelOp] \ r =
        let hoistOpRec = hoistOp(rc, termMap, equalitySets, impossible, idToBool, independentBool);
        match op {
            // We could here keep the BoolExps that we do not want to handle as if, but then we limit
            // later iterations of the query algorithms, or require that this file is changed later
            case Search(rowVar, relSym, body) =>
                let RowVar.Named(id) = rowVar;
                let RelSym.Symbol(_, arity, _) = relSym;
                Vector.forEach(i -> {
                    match MutDisjointSets.find((rowVar, i), equalitySets) {
                        case Some(rep) => MutMap.putWith(_ -> v -> v, rep, RamTerm.RowLoad(rowVar, i, relSym), termMap)
                        case None => bug!("In Fixpoint.Hoisting: Everything should be in the equalitySet")
                    }
                }, Vector.range(0, arity));
                let optHoistedBody = hoistOpRec(body);
                match optHoistedBody {
                    case None => None
                    case Some(hoistedBody) =>
                        let relevant = List.filter(isBoolGround(termMap, equalitySets), MutList.toList(MutMap.getWithDefault(id, MutList.empty(rc), idToBool)));
                        let range = Vector.range(0, arity);
                        // Remove all terms that were bound here.
                        // If there are equalities between 2 variables from the same tuple save them for later
                        let _intraEqualities = MutList.empty(rc);
                        let knownEqualities = MutList.empty(rc);
                        range |> Vector.forEach(i -> {match MutDisjointSets.find((rowVar, i), equalitySets) {
                            case None => ()
                            case Some(rep) => match unwrap(MutMap.get(rep, termMap)) {
                                case RamTerm.RowLoad(rv, i1, rel) =>
                                    if (rv == rowVar) {
                                        MutMap.remove((rv, i1), termMap);
                                        if(i == i1) {
                                            ()
                                        } else {
                                            bug!("Case not handled currently")
                                            // MutList.push((i, i1), intraEqualities)
                                        }
                                    } else 
                                    MutList.push(BoolExp.Eq(RamTerm.RowLoad(rowVar, i, relSym), RamTerm.RowLoad(rv, i1, rel)), knownEqualities)
                                case value => MutList.push(BoolExp.Eq(RamTerm.RowLoad(rowVar, i, relSym), value), knownEqualities)
                        }}});
                        let hoistedToHere =
                            List.filter(x -> not isBoolGround(termMap, equalitySets, x), relevant) |>
                            List.map(simplifyLoadsBool(termMap, equalitySets));
                            // List.toVector;
                        let combined = List.toVector(List.append(hoistedToHere, MutList.toList(knownEqualities)));
                        let newOp = 
                            if (Vector.length(combined) != 0)
                                Query(rowVar, relSym, combined, -1, hoistedBody)
                            else Search(rowVar, relSym, hoistedBody);
                        Some(newOp)
                }
                // MutSet.remove(id, seenRowVars); // Corectness
                // MutMap.remove(id, idToBool); // Not needed anymore
                // Some(newOp)

            // TODO: Do we want to extend behavior?
            case Functional(RowVar.Named(id), func, terms, body, arity) => match hoistOpRec(body) {
                case None => None
                case Some(v) => Some(Functional(RowVar.Named(id), func, terms, v, arity))
            }
            case Project(_, _) => Some(op)
            case If(boolExps, body) => 
                // let insertt = b -> MutList.push(b, independentBool);
                Vector.forEach(b -> {
                    let vars = collectBoolVariables(b);
                    if (Set.size(vars) == 0)
                        MutList.push(b, independentBool) 
                    else
                    // Don't collect Eq's. They are handled separately to ensure we refer to the earliest evaluated expression.
                        Set.forEach(v -> match b {
                            case Eq(_, _) => ()
                            case _ => let boolList = MutMap.getOrElsePut(v, MutList.empty(rc), idToBool);
                            MutList.push(b, boolList)
                        }, vars)
                }, boolExps);
                hoistOpRec(body)
            case Query(_, _, _, _, _) => bug!("Query should not exists when introducing Query")
        }

    @Internal
    def collectBoolVariables(bool: BoolExp): Set[Int32] =  match bool {
        case IsEmpty(_) => Set#{}
        case NotMemberOf(terms, _) => Vector.foldLeft(y -> x -> Set.union(collectTermVariables(x), y), Set#{}, terms)
        case Eq(term1, term2) => Set.union(collectTermVariables(term1), collectTermVariables(term2))
        case Guard0(_) => Set#{}
        case Guard1(_, term1) => collectTermVariables(term1)
        case Guard2(_, term1, term2) => Set.union(collectTermVariables(term1), collectTermVariables(term2))
        case Guard3(_, term1, term2, term3) => 
            Set.union(Set.union(collectTermVariables(term1), collectTermVariables(term2)), collectTermVariables(term3))
        case Guard4(_, term1, term2, term3, term4) => 
            Set.union(Set.union(Set.union(collectTermVariables(term1), collectTermVariables(term2)), collectTermVariables(term3)), collectTermVariables(term4))
        case Guard5(_, term1, term2, term3, term4, term5) => 
            Set.union(Set.union(Set.union(Set.union(collectTermVariables(term1), collectTermVariables(term2)), collectTermVariables(term3)), collectTermVariables(term4)), collectTermVariables(term5))
    }

    @Internal
    def collectTermVariables(term: RamTerm): Set[Int32] = match term {
        case Lit(_, _)                              => Set#{}
        case RowLoad(RowVar.Named(id), _, _)   => Set#{id}
        // case LoadLatVar(RowVar.Named(id), _, _)   => Set#{id}
        case Meet(_, t1, t2, _)                     => Set.union(collectTermVariables(t1), collectTermVariables(t2))
        case App0(_, _)                             => Set#{}
        case App1(_, t1, _)                         => collectTermVariables(t1)
        case App2(_, t1, t2, _)                     => Set.union(collectTermVariables(t1), collectTermVariables(t2))
        case App3(_, t1, t2, t3, _)                 => Set.union(Set.union(collectTermVariables(t1), collectTermVariables(t2)), collectTermVariables(t3))
        case App4(_, t1, t2, t3, t4, _)             => Set.union(Set.union(Set.union(collectTermVariables(t1), collectTermVariables(t2)), collectTermVariables(t3)), collectTermVariables(t4))
        case App5(_, t1, t2, t3, t4, t5, _)         => Set.union(Set.union(Set.union(Set.union(collectTermVariables(t1), collectTermVariables(t2)), collectTermVariables(t3)), collectTermVariables(t4)), collectTermVariables(t5))
    }

    @Internal
    def simplifyLoadsBool(
        termMap: MutMap[Load, RamTerm, r],
        equalitySets: MutDisjointSets[Load, r], 
        bool: BoolExp
    ): BoolExp \ r = 
    let simplifyTerm = simplifyLoadsTerm(termMap, equalitySets);
    match bool {
        case IsEmpty(_) => bool
        case NotMemberOf(_, _) => bool
        case Eq(t1, t2) => Eq(simplifyTerm(t1), simplifyTerm(t2))
        case Guard0(_) => bool
        case Guard1(f, t1) => Guard1(f, simplifyTerm(t1))
        case Guard2(f, t1, t2) => Guard2(f, simplifyTerm(t1), simplifyTerm(t2))
        case Guard3(f, t1, t2, t3) => Guard3(f, simplifyTerm(t1), simplifyTerm(t2), simplifyTerm(t3))
        case Guard4(f, t1, t2, t3, t4) => Guard4(f, simplifyTerm(t1), simplifyTerm(t2), simplifyTerm(t3), simplifyTerm(t4))
        case Guard5(f, t1, t2, t3, t4, t5) => Guard5(f, simplifyTerm(t1), simplifyTerm(t2), simplifyTerm(t3), simplifyTerm(t4), simplifyTerm(t5))
    }

    @Internal
    def simplifyLoadsTerm(
        termMap: MutMap[Load, RamTerm, r],
        equalitySets: MutDisjointSets[Load, r], 
        term: RamTerm
    ): RamTerm \ r = 
    let recurse = simplifyLoadsTerm(termMap, equalitySets);
    match term {
        case Lit(_, _) => term
        case RowLoad(tv, index, _) => match MutMap.get(unwrap(MutDisjointSets.find((tv, index), equalitySets)), termMap) {
            case Some(v) => v
            case None => term
        }
        case Meet(f, t1, t2, id) => Meet(f, recurse(t1), recurse(t2), id)
        case App0(_, _) => term
        case App1(f, t1, id) => App1(f, recurse(t1), id)
        case App2(f, t1, t2, id) => App2(f, recurse(t1), recurse(t2), id)
        case App3(f, t1, t2, t3, id) => App3(f, recurse(t1), recurse(t2), recurse(t3), id)
        case App4(f, t1, t2, t3, t4, id) => App4(f, recurse(t1), recurse(t2), recurse(t3), recurse(t4), id)
        case App5(f, t1, t2, t3, t4, t5, id) => App5(f, recurse(t1), recurse(t2), recurse(t3), recurse(t4), recurse(t5), id)
    }

    @Internal
    def isBoolGround(
        termMap: MutMap[Load, RamTerm, r],
        equalitySets: MutDisjointSets[Load, r], 
        bool: BoolExp
    ): Bool \ r =
        let termGround = isTermGround(termMap, equalitySets);
        match bool {
            case IsEmpty(_) => true // Should not happen. TODO: Perhaps throw an error?
            case NotMemberOf(terms, _) => Vector.forAll(termGround, terms)
            case Eq(term1, term2) => termGround(term1) and termGround(term2)
            case Guard0(_) => true
            case Guard1(_, term1) => termGround(term1)
            case Guard2(_, term1, term2) => termGround(term1) and termGround(term2)
            case Guard3(_, term1, term2, term3) => termGround(term1) and termGround(term2) and termGround(term3)
            case Guard4(_, term1, term2, term3, term4) => termGround(term1) and termGround(term2) and termGround(term3) and termGround(term4)
            case Guard5(_, term1, term2, term3, term4, term5) => termGround(term1) and termGround(term2) and termGround(term3) and termGround(term4) and termGround(term5)
    }

    @Internal
    def isTermGround(
        termMap: MutMap[Load, RamTerm, r],
        equalitySets: MutDisjointSets[Load, r],
        term: RamTerm
    ): Bool \ r =
        let termGround = isTermGround(termMap, equalitySets);
        match term {
            case Lit(_, _) => true
            case RowLoad(tv, i, _) =>
                MutMap.memberOf(unwrap(MutDisjointSets.find((tv, i), equalitySets)), termMap)
            // case LoadLatVar(RowVar.Named(id), _, _) => Set.memberOf(id)
            case Meet(_, t1, t2, _) => termGround(t1) and termGround(t2)
            case App0(_, _) => true
            case App1(_, t1, _) => termGround(t1)
            case App2(_, t1, t2, _) => termGround(t1) and termGround(t2)
            case App3(_, t1, t2, t3, _) => termGround(t1) and termGround(t2) and termGround(t3)
            case App4(_, t1, t2, t3, t4, _) => termGround(t1) and termGround(t2) and termGround(t3) and termGround(t4)
            case App5(_, t1, t2, t3, t4, t5, _) => termGround(t1) and termGround(t2) and termGround(t3) and termGround(t4) and termGround(t5)
        }

    def collectLoads(rowVar: RowVar, arity: Int32, equalitySets: MutDisjointSets[Load, r]): Unit \ r = 
        Vector.forEach(i -> MutDisjointSets.makeSet((rowVar, i), equalitySets), Vector.range(0, arity))

    def unifyEqualitiesStmt(
        equalitySets: MutDisjointSets[Load, r], 
        constEqualities: MutMap[Load, List[(Boxed, RamId)], r],
        stmt: RamStmt
    ): Unit \ r = match stmt {
        case RamStmt.Seq(xs) => Vector.forEach(unifyEqualitiesStmt(equalitySets, constEqualities), xs)
        case RamStmt.Insert(op) => unifyEqualitiesOp(equalitySets, constEqualities, op)
        case RamStmt.Par(xs) => Vector.forEach(unifyEqualitiesStmt(equalitySets, constEqualities), xs)
        case RamStmt.Until(boolExps, body) =>
            Vector.forEach(boolExp -> unifyBoolExp(equalitySets, constEqualities, boolExp), boolExps);
            unifyEqualitiesStmt(equalitySets, constEqualities, body)
        case RamStmt.Merge(_, _) => ()
        case RamStmt.Swap(_, _) => ()
        case RamStmt.Purge(_) => ()
        case RamStmt.Comment(_) => ()
    }

    def unifyBoolExp(
            equalitySets: MutDisjointSets[Load, r],
            constEqualities: MutMap[Load, List[(Boxed, RamId)], r],
            boolExp: BoolExp): Unit \ r = match boolExp {
        case Eq(RamTerm.RowLoad(tv1, i1, _), RamTerm.RowLoad(tv2, i2, _)) => 
            MutDisjointSets.makeSet((tv1, i1), equalitySets);
            MutDisjointSets.makeSet((tv2, i2), equalitySets);
            MutDisjointSets.union((tv1, i1), (tv2, i2), equalitySets)
        case Eq(RamTerm.RowLoad(tv, i, _), RamTerm.Lit(val, id)) => 
            MutMap.putWith(_ -> list -> (val, id) :: list, (tv, i), (val, id) :: Nil, constEqualities)
        case Eq(RamTerm.Lit(val, id), RamTerm.RowLoad(tv, i, _)) => 
            MutMap.putWith(_ -> list -> (val, id) :: list, (tv, i), (val, id) :: Nil, constEqualities)
        case _ => ()
    }

    def unifyEqualitiesOp(
        equalitySets: MutDisjointSets[Load, r], 
        constEqualities: MutMap[Load, List[(Boxed, RamId)], r],
        op: RelOp
    ): Unit \ r = match op {   
        case RelOp.Search(rowVar, RelSym.Symbol(_, arity, _), body) => 
            collectLoads(rowVar, arity, equalitySets);
            unifyEqualitiesOp(equalitySets, constEqualities, body)
        case RelOp.Query(_, _, _, _, _) => 
            bug!("In Hoisting.unifyEqualitiesOp: Query should not exist at this point!")
        case RelOp.Functional(rowVar, _, _, body, arity) => 
            collectLoads(rowVar, arity, equalitySets);
            unifyEqualitiesOp(equalitySets, constEqualities, body)
        case RelOp.Project(_, _) => ()
        case RelOp.If(boolExps, body) =>
            Vector.forEach(unifyBoolExp(equalitySets, constEqualities), boolExps);
            unifyEqualitiesOp(equalitySets, constEqualities, body)
    }

    def unwrap(opt: Option[a]): a = match opt {
        case Some(v) => v
        case None => bug!("Bug in hoisting")
    }
}