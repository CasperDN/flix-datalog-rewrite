mod Fixpoint.Phase.IndexSelection2 {
    use Fixpoint.Ast.AugmentedRam.{RamStmt, RelOp, RelSym, RamTerm, BoolExp, TupleVar, AugmentedProgram}
    use Fixpoint.Ast.AugmentedRam.RelOp.{Search, SearchWithIndex, Functional, Project, If}
    use Fixpoint.Ast.AugmentedRam.BoolExp.{IsEmpty, NotMemberOf, Eq, Leq, Guard0, Guard1, Guard2, Guard3, Guard4, Guard5}
    use Fixpoint.Ast.AugmentedRam.RamTerm.{Lit, RowLoad, Meet, App0, App1, App2, App3, App4, App5}

    // Hoist if-constructions as far as possible and merge into SearchWithQuery when possible/relevant.
    // TODO: We could use a disjoin set datastructure to move up and minimize the number of equalities needed
    @Internal
    pub def queryProgram(program: AugmentedProgram): AugmentedProgram = match program { 
        case AugmentedProgram.Program(stmt, facts, meta, _) => 
            
            AugmentedProgram.Program(queryStmt(stmt), facts, meta, ???)
    }

    @Internal
    pub def queryStmt(stmt: RamStmt): RamStmt = match stmt {
        case RamStmt.Insert(op) => region rc {
            let independent = MutList.empty(rc);
            let newOp = queryOp(op, rc, MutSet.empty(rc), MutMap.empty(rc), independent);
            if(MutList.size(independent) == 0) 
                RamStmt.Insert(newOp) else RamStmt.Insert(If(MutList.toVector(independent), newOp))
        }
        case RamStmt.Seq(xs) => Vector.map(x -> queryStmt(x), xs) |> RamStmt.Seq
        case RamStmt.Par(xs) => Vector.map(x -> queryStmt(x), xs) |> RamStmt.Seq
        case RamStmt.Until(test, body) => RamStmt.Until(test, queryStmt(body))

        case RamStmt.Merge(_, _) => stmt
        case RamStmt.Swap(_, _) => stmt
        case RamStmt.Purge(_) => stmt
        case RamStmt.Comment(_) => stmt
    }

    /// Takes the relative operator, op, region rc, and tuple-vars defined so far, seenTupleVars 
    /// Rewrites the relative operator, op, as the first return value, and a map from tuple-vars to 
    @Internal
    def queryOp(op: RelOp, rc: Region[r], seenTupleVars: MutSet[Int32, r], idToBool: MutMap[Int32, MutList[BoolExp, r], r], independentBool: MutList[BoolExp, r]): RelOp \ r = 
        let recursiveCall = x -> queryOp(x, rc, seenTupleVars, idToBool, independentBool);
        match op {
        // We could here keep the BoolExps that we do not want to handle as if, but then we limit later iterations of the query algorithms, or require that this file is changed later
            case Search(TupleVar.Named(id), relSym, rest) => 
                MutSet.add(id, seenTupleVars);
                let newRest = recursiveCall(rest);

                let newOp = match MutMap.get(id, idToBool) {
                    case Some(v) => 
                    let seenAsSet = MutSet.toSet(seenTupleVars);
                    let relevant = List.filter(x -> isBoolGround(x, seenAsSet), MutList.toList(v));
                    MutSet.remove(id, seenTupleVars);
                    let seenWithoutCurrent = MutSet.toSet(seenTupleVars);
                    let hoistedToHere = List.toVector(List.filter(x -> not isBoolGround(x, seenWithoutCurrent), relevant));
                    SearchWithIndex(TupleVar.Named(id), relSym, hoistedToHere, newRest)


                    case None => Search(TupleVar.Named(id), relSym, newRest)
                };
                MutSet.remove(id, seenTupleVars); // Corectness
                MutMap.remove(id, idToBool); // Not needed anymore
                newOp

            // TODO: Do we want to extend behavior?
            case Functional(TupleVar.Named(id), func, terms, rest, arity, inId) => Functional(TupleVar.Named(id), func, terms, recursiveCall(rest), arity, inId)
            case Project(_, _) => op
            case If(boolExps, rest) => 
                // let insertt = b -> MutList.push(b, independentBool);
                Vector.forEach(b -> {
                    let vars = collectBoolVariables(b);
                    // Vector.forEach(v -> if (Set.size(vars) == 0) () else (), vars)

                    // Vector.forEach(v -> if (Set.size(vars) == 0) {MutList.append(b, independentBool); ()} else (), vars)
                    if (Set.size(vars) == 0)
                        MutList.push(b, independentBool) 
                    else 
                        Set.forEach(v -> {
                            let boolList = MutMap.getOrElsePut(v, MutList.empty(rc), idToBool);
                            MutList.push(b, boolList)
                        }, vars)
                }, boolExps);
                recursiveCall(rest)
            case SearchWithIndex(_, _, _, _) => bug!("SearchWithIndex should not exists when introducing SearchWithIndex")
        }


    @Internal
    def collectBoolVariables(bool: BoolExp): Set[Int32] = 
        match bool {
            case IsEmpty(_) => Set#{}
            case NotMemberOf(terms, _) => Vector.foldLeft(y -> x -> Set.union(collectTermVariables(x), y), Set#{}, terms)
            case Eq(term1, term2) => Set.union(collectTermVariables(term1), collectTermVariables(term2))
            case Leq(_, term1, term2) => Set.union(collectTermVariables(term1), collectTermVariables(term2))
            case Guard0(_) => Set#{}
            case Guard1(_, term1) => collectTermVariables(term1)
            case Guard2(_, term1, term2) => Set.union(collectTermVariables(term1), collectTermVariables(term2))
            case Guard3(_, term1, term2, term3) => Set.union(Set.union(collectTermVariables(term1), collectTermVariables(term2)), collectTermVariables(term3))
            case Guard4(_, term1, term2, term3, term4) => Set.union(Set.union(Set.union(collectTermVariables(term1), collectTermVariables(term2)), collectTermVariables(term3)), collectTermVariables(term4))
            case Guard5(_, term1, term2, term3, term4, term5) => Set.union(Set.union(Set.union(Set.union(collectTermVariables(term1), collectTermVariables(term2)), collectTermVariables(term3)), collectTermVariables(term4)), collectTermVariables(term5))
    }

    @Internal
    def collectTermVariables(term: RamTerm): Set[Int32] = match term {
        case Lit(_, _)                              => Set#{}
        case RowLoad(TupleVar.Named(id), _, _)   => Set#{id}
        // case LoadLatVar(TupleVar.Named(id), _, _)   => Set#{id}
        case Meet(_, t1, t2, _)                     => Set.union(collectTermVariables(t1), collectTermVariables(t2))
        case App0(_, _)                             => Set#{}
        case App1(_, t1, _)                         => collectTermVariables(t1)
        case App2(_, t1, t2, _)                     => Set.union(collectTermVariables(t1), collectTermVariables(t2))
        case App3(_, t1, t2, t3, _)                 => Set.union(Set.union(collectTermVariables(t1), collectTermVariables(t2)), collectTermVariables(t3))
        case App4(_, t1, t2, t3, t4, _)             => Set.union(Set.union(Set.union(collectTermVariables(t1), collectTermVariables(t2)), collectTermVariables(t3)), collectTermVariables(t4))
        case App5(_, t1, t2, t3, t4, t5, _)         => Set.union(Set.union(Set.union(Set.union(collectTermVariables(t1), collectTermVariables(t2)), collectTermVariables(t3)), collectTermVariables(t4)), collectTermVariables(t5))
    }

    @Internal
    def isBoolGround(bool: BoolExp, grounding: Set[Int32]): Bool = 
        let termGround = x -> isTermGround(x, grounding);
        match bool {
            case IsEmpty(_) => true // Should not happen. TODO: Perhaps throw an error?
            case NotMemberOf(terms, _) => Vector.forAll(termGround, terms)
            case Eq(term1, term2) => termGround(term1) and termGround(term2)
            case Leq(_, term1, term2) => termGround(term1) and termGround(term2)
            case Guard0(_) => true
            case Guard1(_, term1) => termGround(term1)
            case Guard2(_, term1, term2) => termGround(term1) and termGround(term2)
            case Guard3(_, term1, term2, term3) => termGround(term1) and termGround(term2) and termGround(term3)
            case Guard4(_, term1, term2, term3, term4) => termGround(term1) and termGround(term2) and termGround(term3) and termGround(term4)
            case Guard5(_, term1, term2, term3, term4, term5) => termGround(term1) and termGround(term2) and termGround(term3) and termGround(term4) and termGround(term5)
    }

    @Internal
    def isTermGround(term: RamTerm, grounding: Set[Int32]): Bool = match term {
        case Lit(_, _) => true
        case RowLoad(TupleVar.Named(id), _, _)   => Set.memberOf(id, grounding)
        // case LoadLatVar(TupleVar.Named(id), _, _)   => Set.memberOf(id, grounding)
        case Meet(_, t1, t2, _)                     => isTermGround(t1, grounding) and isTermGround(t2, grounding)
        case App0(_, _)                             => true
        case App1(_, t1, _)                         => isTermGround(t1, grounding)
        case App2(_, t1, t2, _)                     => isTermGround(t1, grounding) and isTermGround(t2, grounding)
        case App3(_, t1, t2, t3, _)                 => isTermGround(t1, grounding) and isTermGround(t2, grounding) and isTermGround(t3, grounding)
        case App4(_, t1, t2, t3, t4, _)             => isTermGround(t1, grounding) and isTermGround(t2, grounding) and isTermGround(t3, grounding) and isTermGround(t4, grounding)
        case App5(_, t1, t2, t3, t4, t5, _)         => isTermGround(t1, grounding) and isTermGround(t2, grounding) and isTermGround(t3, grounding) and isTermGround(t4, grounding) and isTermGround(t5, grounding)
    }
}