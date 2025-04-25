mod Fixpoint.Phase.JoinProfiler {
    use Fixpoint.Ast.Ram.RamProgram.Program
    use Fixpoint.Ast.Ram.{RamProgram, RamStmt, RelOp, RelSym, RowVar}
    use Fixpoint.Helpers.unwrap
    use Fixpoint.Phase.Hoisting.unifyEqualitiesOp
    use Fixpoint.Counter
    use Fixpoint.Counter.Counter

    pub enum JoinProfile {
        case Profile(Map[RowVar, Vector[Int32]], Map[(RowVar, Vector[Int32]), Vector[Int32]])
    }

    // (non-recursive, recursive rules)
    type alias Rules = (List[RelOp], List[RelOp])

    pub def profileProgram(program: RamProgram): JoinProfile = {
        
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

    def collectBoundVars(vars: List[(RowVar, RelSym)], rule: RelOp): Map[(RowVar, RelSym), List[Vector[Int32]]] = region rc {
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
            let collectedSoFar = MutMap.getOrElsePut((???, relSym), MutSet.empty(rc), attributesForRelSym);
            MutSet.addAll(MutSet.toSet(result), collectedSoFar)
        });
        attributesForRelSym |> MutMap.toMap |> Map.map(x -> x |> MutSet.toList |> List.map(List.toVector))
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

    def estimateToCollect(rc: Region[r], toEstimate: Map[(RowVar, RelSym), List[Search]], collectFor: MutMap[(RelSym, Search), MutSet[RowVar, r], r]): Unit \ r =
        Map.forEach(match (rowVar, relSym) -> val -> {
            val |> List.forEach(search ->
                MutMap.getOrElsePut((relSym, search), MutSet.empty(rc), collectFor) |>
                MutSet.add(rowVar)
            )
        }, toEstimate)

    def collectedToEstimateStmts(counter: Counter[r], rowVarToPos: MutMap[(RowVar, Search), Int32, r], collectFor: MutMap[(RelSym, Search), MutSet[RowVar, r], r]): List[RamStmt] \ r =
        collectFor |> MutMap.foldLeftWithKey(acc -> match (relSym, search) -> rowVars -> {
            let savePos = Counter.getNewID(counter);
            MutSet.forEach(rowVar -> MutMap.put((rowVar, search), savePos, rowVarToPos), rowVars);
            RamStmt.EstimateJoinSize(relSym, -1, savePos, search) :: acc
        }, Nil)

    def instrumentProgram(rc: Region[r], program: RamProgram): RamProgram \ r = {
        let counter = Counter.fresh(rc);
        let rowVarToPos = MutMap.empty(rc);
        def collectUntilBody(collectFor, s) = match s {
            case RamStmt.Insert(op) =>
                let toEstimate = collectBoundVars(collectRowVarRelSyms(Nil, op), op);
                estimateToCollect(rc, toEstimate, collectFor)
                // Map.forEach(match (rowVar, relSym) -> val -> {
                //     val |> List.forEach(search ->
                //         MutMap.getOrElsePut((relSym, search), MutSet.empty(rc), collectFor) |>
                //         MutSet.add(rowVar)
                //         // let positionInArr =
                //         // RamStmt.EstimateJoinSize(relSym, -1, UniqueInts.getIndex(rowVar, rowVarToPos), List.toVector(search))
                //     )
                // }, toEstimate)
            case RamStmt.Merge(_, _) => ()
            case RamStmt.Swap(_, _) => ()
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(collectUntilBody(collectFor), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(collectUntilBody(collectFor), stmts)
            case RamStmt.Until(conditions, body) => bug!("bug in Fixpoint.Phase.JoinProfiler: Nested until statements should not exist")
            case RamStmt.Comment(_) => ()
            case RamStmt.EstimateJoinSize(_, _, _, _) => bug!("bug in Fixpoint.Phase.JoinProfiler: EstimateJoinSize should not exist at this point")
        };

        // Note that estimation can be done in parallel with the expressions using them.
        // Even for statements outside the until blocks they only write to the new versions.
        // This means that we require the compiler to not change any indexes used in a given
        // par statement. This might seem like an of course, but it would not necessarily be
        // unsafe to do so.
        def instrumentStmt(s: RamStmt): RamStmt = match s {
            case RamStmt.Insert(op) =>
                // We estimate the size immediately before the insert-loop
                let toEstimate = collectBoundVars(collectRowVarRelSyms(Nil, op), op);
                // Collect information for RelSym with search and save it for RowVar.
                let collectFor = MutMap.empty(rc);
                estimateToCollect(rc, toEstimate, collectFor);
                let estimateStmts = collectedToEstimateStmts(counter, rowVarToPos, collectFor);
                if(List.isEmpty(estimateStmts)) {
                    s
                } else {
                    List.reverse(s :: estimateStmts) |> 
                    List.toVector |>
                    RamStmt.Par
                }
            case RamStmt.Merge(_, _) => s
            case RamStmt.Swap(_, _) => s
            case RamStmt.Purge(_) => s
            case RamStmt.Seq(stmts) => Vector.map(instrumentStmt, stmts) |> RamStmt.Seq
            case RamStmt.Par(stmts) => Vector.map(instrumentStmt, stmts) |> RamStmt.Par
            case RamStmt.Until(conditions, body) => RamStmt.Until(conditions, instrumentStmt(body))
            case RamStmt.Comment(_) => s
            case RamStmt.EstimateJoinSize(_, _, _, _) => bug!("bug in Fixpoint.Phase.JoinProfiler: EstimateJoinSize should not exist at this point")
        };
        let Program(mainStmt, facts, predState, indexes) = program;
        // This should be perhaps 0.1%-10% of the original facts.
        let newFacts = ???;

        Program(instrumentStmt(mainStmt), newFacts, predState, indexes)
    }
    
    

}