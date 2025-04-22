mod Fixpoint.Phase.JoinProfiler {
    use Fixpoint.Ast.Ram.RamProgram.Program
    use Fixpoint.Ast.Ram.{RamProgram, RamStmt, RelOp, RelSym, RowVar}
    use Fixpoint.Helpers.unwrap
    use Fixpoint.Phase.Hoisting.unifyEqualitiesOp

    pub enum JoinProfile {
        case Profile(Map[RowVar, Vector[Int32]], Map[(RowVar, Vector[Int32]), Vector[Int32]])
    }

    // (non-recursive, recursive rules)
    type alias Rules = (List[RelOp], List[RelOp])

    pub def profileProgram(program: RamProgram): JoinProfile = {
        
        ???
    }

    def computeUniqueJoin(program: RamProgram): Unit = {
        let rules = collectRules(program);
        let (nonRecRules, recRules) = rules;
        let _ = nonRecRules |>
        List.forEach(rule -> collectBoundVars(collectRowVarRelSyms(Nil, rule), rule));
        ???
    }

    def collectRowVarRelSyms(collected: List[(RowVar, RelSym)], op: RelOp): List[(RowVar, RelSym)] = match op {
        case RelOp.Search(rowVar, relSym, body) => collectRowVarRelSyms((rowVar, relSym) :: collected, body)
        case RelOp.Query(_, _, _, _, _) => bug!("Bug in Fixpoint.Phase.JoinProfiler: Query should not exist at the current point")
        case RelOp.If(_, body) => collectRowVarRelSyms(collected, body)
        // We do not currently handle functional predicates. Estimating their join size cannot be done in the same way as for normal relations.
        // Functional predicates must always be fully bound. The only question then whether it is cheaper to evaluate the functional predicate few times
        // or evaluate the potential query/search it could be reordered with few times.
        case RelOp.Functional(_, _, _, body, _) => collectRowVarRelSyms(collected, body)
        case RelOp.Project(_, _) => collected

    }

    def collectBoundVars(vars: List[(RowVar, RelSym)], rule: RelOp): Map[RowVar, List[List[Int32]]] = region rc {
        let equalities =  MutDisjointSets.empty(rc);
        let constEqualities =  MutMap.empty(rc);
        unifyEqualitiesOp(equalities, constEqualities, rule);
        // equivalentMap is basically a SIP-graph.
        let equivalentMap = MutMap.empty(rc);
        vars |>
        List.forEach(match (rv, RelSym.Symbol(_, arity, _)) -> {
            Vector.range(0, arity) |>
            Vector.forEach(i -> 
                let load = (rv, arity);
                let rep = unwrap(MutDisjointSets.find(load, equalities));
                if (rep == load)
                    ()
                else {
                    MutMap.putWith(_ -> oldVal -> load :: oldVal, rep, load :: Nil, equivalentMap)
                }
            )
        });
        let attributesForRelSym = MutMap.empty(rc);
        let _ = vars |> List.forEach(match (rvi, relSym) ->{
            let boundForI = MutSet.empty(rc);
            vars |>
            List.forEach(aj ->
                let (rvj, RelSym.Symbol(_, arity, _)) = aj;
                let boundByJ = MutSet.empty(rc);
                Vector.range(0, arity) |>
                Vector.forEach(i ->
                    unwrap(MutMap.get((rvj, i), equivalentMap)) |>
                    List.forEach(match (rv, index) -> 
                        if(rv == rvi)
                            MutSet.add(index, boundByJ)
                        else ()
                    )
                );
                MutSet.add(MutSet.toList(boundByJ), boundForI)
            );
            let result = MutSet.empty(rc);
            powerSetForEach(List.toVector(MutSet.toList(boundForI)), result);
            let collectedSoFar = MutMap.getOrElsePut(relSym, MutSet.empty(rc), attributesForRelSym);
            MutSet.addAll(MutSet.toSet(result), collectedSoFar)
        });
        attributesForRelSym |> MutMap.map(MutSet.toList) |> MutMap.toMap
    }

    def powerSetForEach(values: Vector[List[Int32]], setForJ: MutSet[List[Int32], r]): Unit \ r =
        def loop(index, val) = 
            if(Vector.size(values) == index) {
                let toInsert = Set.foldRight(boundVar -> acc -> boundVar :: acc, Nil, val);
                MutSet.add(toInsert, setForJ)
            } else {
                Vector.range(index + 1, Vector.length(values) + 1) |> 
                Vector.forEach(nextIndex -> {
                    let newVal = List.foldLeft(acc -> boundVar -> Set.insert(boundVar, acc), val, Vector.get(index, values));     
                    // let newVal = ???;
                    loop(nextIndex, newVal)
                })
            };
        loop(0, Set.empty())


    def instrumentProgram(program: RamProgram, counter: Counter[r]): RamProgram \ r = {
        def instrumentStmt(s: RamStmt): RamStmt = match s {
            case RamStmt.Insert(op) => 
            // We estimate the size immediately before the insert-loop
            let toEstimate = collectBoundVars(collectRowVarRelSyms(Nil, op), op);
            // TODO: Make a map from (relSym, search) to the counter-position.
            Map.forEach(relSym -> val -> {
                val |> List.forEach(search ->
                RamStmt.EsitmateJoinSize(relSym, -1, Counter.getNewID(counter), List.toVector(search)))
            });
            ???
            case RamStmt.Merge(_, _) => s
            case RamStmt.Swap(_, _) => s
            case RamStmt.Purge(_) => s
            case RamStmt.Seq(stmts) => Vector.map(instrumentStmt, stmts) |> RamStmt.Seq
            case RamStmt.Par(stmts) => Vector.map(instrumentStmt, stmts) |> RamStmt.Par
            case RamStmt.Until(conditions, body) => RamStmt.Until(conditions, instrumentStmt(body))
            case RamStmt.Comment(_) => s
            case RamStmt.EstimateJoinSize(_, _, _, _) => bug!("bug in Fixpoint.Phase.JoinProfiler: EstimateJoinSize should not exist at this point")
        };
        let Program(mainStmt, _, _, _) = program;
        instrumentStmt((Nil, Nil), false, mainStmt)
    }
    
    

}