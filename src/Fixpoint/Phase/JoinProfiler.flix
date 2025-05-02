mod Fixpoint.Phase.JoinProfiler {
    use Fixpoint.Ast.Ram.{RamProgram, RamStmt, RelOp, RelSym, RowVar, collectRowVarRelSymOp}
    use Fixpoint.Counter
    use Fixpoint.Counter.Counter
    use Fixpoint.Helpers.unwrap
    use Fixpoint.Phase.Hoisting.unifyEqualitiesOp
    use Fixpoint.Solver

    @Internal
    pub enum JoinProfile {
        case Profile(
            Map[RowVar, Vector[Int64]], 
            Map[(RowVar, Vector[Int32]), Vector[Int64]]
        )
    }

    // (non-recursive, recursive rules)
    type alias Rules = (List[RelOp], List[RelOp])

    @Internal
    pub def profileProgram(program: RamProgram): (JoinProfile, Map[RowVar, Map[RowVar, Set[Int32]]]) = region rc {
        let (instrumentedProgram, attributeMap, rowVarToPos) = instrumentProgram(rc, program); 
        let _ = Fixpoint.Debugging.notifyPreLowering("Join Profiler", instrumentedProgram);
        let vec = Solver.runJoinProfiler(instrumentedProgram);
        let joinToSizeDup = Map.map(i -> Vector.get(i, vec), rowVarToPos);
        let sizePerIter = joinToSizeDup |> 
            Map.foldLeftWithKey(acc -> k1 -> v1 -> {
                let k2 = fst(k1);
                let v2 = Vector.map(fst >> Int32.toInt64, v1);
                Map.insert(k2, v2, acc)
            }, Map#{});
        let expectedJoinSize = Map.map(Vector.map(snd >> Int32.toInt64), joinToSizeDup);
        let profile = JoinProfile.Profile(sizePerIter, expectedJoinSize);
        (profile, attributeMap)
    }

    def collectBoundVars(
        rc: Region[r], 
        vars: List[(RowVar, RelSym)], 
        attributeMap: MutMap[RowVar, MutMap[RowVar, MutSet[Int32, r], r], r], 
        rule: RelOp
    ): Map[(RowVar, RelSym), List[Vector[Int32]]] \ r =
        let equalities =  MutDisjointSets.empty(rc);
        let constEqualities =  MutMap.empty(rc);
        unifyEqualitiesOp(equalities, constEqualities, rule);
        // equivalentMap is basically a SIP-graph.
        let equivalentMap = MutMap.empty(rc);
        vars |>
        List.forEach(match (rv, RelSym.Symbol(_, arity, _)) -> {
            Vector.range(0, arity) |>
            Vector.forEach(i -> 
                let load = (rv, i);
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
            let mapForI = MutMap.getOrElsePut(rvi, MutMap.empty(rc), attributeMap);
            let boundForI = MutSet.empty(rc);
            vars |>
            List.forEach(aj ->
                let (rvj, RelSym.Symbol(_, arity, _)) = aj;
                let boundByJ = MutSet.empty(rc);
                Vector.range(0, arity) |>
                Vector.forEach(i ->
                    match MutMap.get((rvj, i), equivalentMap) {
                        case None => ()
                        case Some(v) => 
                            v |>
                            List.forEach(match (rv, index) -> 
                                if(rv == rvi)
                                    MutSet.add(index, boundByJ)
                                else ()
                            )
                    }
                );
                // We should never encounter rvj again with rvi.
                MutMap.put(rvj, boundByJ, mapForI);
                // MutMap.putWith(_ -> old -> MutSet.add(boundByJ, old), rvj, boundByJ, mapForI);
                MutSet.add(MutSet.toList(boundByJ), boundForI)
            );
            let result = MutSet.empty(rc);
            powerSetForEach(List.toVector(MutSet.toList(boundForI)), result);
            let collectedSoFar = MutMap.getOrElsePut((rvi, relSym), MutSet.empty(rc), attributesForRelSym);
            MutSet.addAll(MutSet.toSet(result), collectedSoFar)
        });
        attributesForRelSym |> MutMap.toMap |> Map.map(x -> x |> MutSet.toList |> List.map(List.toVector))

    def powerSetForEach(values: Vector[List[Int32]], setForJ: MutSet[List[Int32], r]): Unit \ r =
        def loop(index, val) = 
            if(Vector.size(values) == index) {
                let toInsert = Set.foldRight(boundVar -> acc -> boundVar :: acc, Nil, val);
                MutSet.add(toInsert, setForJ)
            } else {
                Vector.range(index + 1, Vector.length(values) + 1) |> 
                Vector.forEach(nextIndex -> {
                    let newVal = List.foldLeft(acc -> boundVar -> Set.insert(boundVar, acc), val, Vector.get(index, values));     
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

    def combineStmtWithEstimate(counter: Counter[r], rowVarToPos: MutMap[(RowVar, Search), Int32, r], collectFor: MutMap[(RelSym, Search), MutSet[RowVar, r], r], stmt: RamStmt): RamStmt \ r = {
        let estimateStmts = collectedToEstimateStmts(counter, rowVarToPos, collectFor);
        if(List.isEmpty(estimateStmts)) {
            stmt
        } else {
            List.reverse(stmt :: estimateStmts) |> 
            List.toVector |>
            RamStmt.Par
        }
    }

    def instrumentProgram(
        rc: Region[r], 
        program: RamProgram
    ): (RamProgram, Map[RowVar, Map[RowVar, Set[Int32]]], Map[(RowVar, Vector[Int32]), Int32]) \ r = {
        let counter = Counter.fresh(rc);
        let rowVarToPos = MutMap.empty(rc);
        let attributeMap = MutMap.empty(rc);
        def collectUntilBody(collectFor, s) = match s {
            case RamStmt.Insert(op) =>
                let toEstimate = collectBoundVars(rc, collectRowVarRelSymOp(op), attributeMap, op);
                estimateToCollect(rc, toEstimate, collectFor)
            case RamStmt.Merge(_, _) => ()
            case RamStmt.Swap(_, _) => ()
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(collectUntilBody(collectFor), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(collectUntilBody(collectFor), stmts)
            case RamStmt.Until(_, _) => bug!("bug in Fixpoint.Phase.JoinProfiler: Nested until statements should not exist")
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
                let toEstimate = collectBoundVars(rc, collectRowVarRelSymOp(op), attributeMap, op);
                // Collect information for RelSym with search and save it for RowVar.
                let collectFor = MutMap.empty(rc);
                estimateToCollect(rc, toEstimate, collectFor);
                combineStmtWithEstimate(counter, rowVarToPos, collectFor, s)
            case RamStmt.Merge(_, _) => s
            case RamStmt.Swap(_, _) => s
            case RamStmt.Purge(_) => s
            case RamStmt.Seq(stmts) => Vector.map(instrumentStmt, stmts) |> RamStmt.Seq
            case RamStmt.Par(stmts) => Vector.map(instrumentStmt, stmts) |> RamStmt.Par
            case RamStmt.Until(conditions, body) => 
                let collectFor = MutMap.empty(rc);
                collectUntilBody(collectFor, body);
                let newBody = combineStmtWithEstimate(counter, rowVarToPos, collectFor, s);
                RamStmt.Until(conditions, newBody)
            case RamStmt.Comment(_) => s
            case RamStmt.EstimateJoinSize(_, _, _, _) => bug!("bug in Fixpoint.Phase.JoinProfiler: EstimateJoinSize should not exist at this point")
        };
        let RamProgram.Program(mainStmt, facts, predState, indexes) = program;
        let instrumentedStmt = instrumentStmt(mainStmt);
        let collectedAttributeMap = attributeMap |> 
            MutMap.map(rc, innerMap -> innerMap |> MutMap.map(rc, MutSet.toSet) |> MutMap.toMap) |> 
            MutMap.toMap;
        unchecked_cast(println(instrumentedStmt) as _ \ r);
        let instrumentedProgram = RamProgram.Program(instrumentedStmt, facts, predState, indexes);
        (instrumentedProgram, collectedAttributeMap, rowVarToPos |> MutMap.toMap)
    }

}