mod Fixpoint.Phase.JoinProfiler {
    use Fixpoint.Counter
    use Fixpoint.Ast.Ram.{RamProgram, RamStmt, RelOp, RelSym, RowVar}
    use Fixpoint.Ast.Ram.RamProgram.Program
    use Fixpoint.Helpers.unwrap
    use Fixpoint.Phase.Hoisting.unifyEqualitiesOp

    // (non-recursive, recursive rules)
    type alias Rules = (List[RelOp], List[RelOp])

    pub def joinOptimize(program: RamProgram): RamProgram = {
        
        ???
    }

    def computeUniqueJoin(program: RamProgram): Unit = {
        let rules = collectRules(program);
        let (nonRecRules, recRules) = rules;
        let _ = nonRecRules |>
        List.forEach(_ -> ());
        ???
    }

    def collectBoundVars(rule: RelOp, vars: Set[(RowVar, RelSym)]): Unit = region rc {
        let equalities =  MutDisjointSets.empty(rc);
        let constEqualities =  MutMap.empty(rc);
        unifyEqualitiesOp(equalities, constEqualities, rule);
        // equivalentMap is basically a graph.
        let equivalentMap = MutMap.empty(rc);
        vars |>
        Set.forEach(match (rv, RelSym.Symbol(_, arity, _)) -> {
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

        let _ = vars |> Set.forEach(ai ->
            let boundForI = MutSet.empty(rc);
            vars |>
            Set.forEach(aj ->
                let (rvj, RelSym.Symbol(_, arity, _)) = aj;
                let boundByJ = MutSet.empty(rc);
                Vector.range(0, arity) |>
                Vector.forEach(i ->
                    unwrap(MutMap.get((rvj, i), equivalentMap)) |>
                    List.forEach(match (rv, index) -> 
                        if(rv == rvj)
                            MutSet.add(index, boundByJ)
                        else ()
                    )
                );
                MutSet.add(MutSet.toList(boundByJ), boundForI)
            )
        );
        ???
    }

    def powerSetForEach(values: Vector[Int32], val: Set[Int32]): Unit  =
        def loop(index, val) = 
            if(Vector.length(values) == index) 
                ???
                // val
            else
                foreach(nextIndex <- Vector.range(index + 1, Vector.length(values)))
                    loop(nextIndex, Set.insert(Vector.get(index, values), val));
                    // yield Set.union(List.toSet(x), y);
        loop(0, Set.empty())


    def collectRules(program: RamProgram): Rules = {
        def collectLoop(rules: Rules, inUntil: Bool, s: RamStmt): Rules = match s {
            case RamStmt.Insert(op) => 
                let (nonRecursive, recursive) = rules;
                if (inUntil) 
                    (nonRecursive, op :: recursive)
                else 
                    (op :: nonRecursive, recursive)
            case RamStmt.Merge(_, _) => rules
            case RamStmt.Swap(_, _) => rules
            case RamStmt.Purge(_) => rules
            case RamStmt.Seq(stmts) => Vector.foldLeft(acc -> collectLoop(acc, inUntil), rules, stmts)
            case RamStmt.Par(stmts) => Vector.foldLeft(acc -> collectLoop(acc, inUntil), rules, stmts)
            case RamStmt.Until(_, body) => collectLoop(rules, true, body)
            case RamStmt.Comment(_) => rules
            case RamStmt.EstimateJoinSize(_, _, _, _) => rules
        };
        let Program(mainStmt, _, _, _) = program;
        collectLoop((Nil, Nil), false, mainStmt)
    }
    
    pub def estimateJoinSize(rc: Region[r], _rel: RelSym, attr: Vector[Int32]): Int32 \ r = 
        let index = ???;
        let prevRef = Ref.fresh(rc, None);
        let dupRef = Counter.fresh(rc);
        let sizeRef = Counter.fresh(rc);
        index |> BPlusTree.forEach(curr -> _ -> {
            let isDup = 
                Ref.get(prevRef) |> 
                Option.exists(prev -> 
                    attr |> Vector.forAll(i -> Array.get(i, prev) == Array.get(i, curr))
                );
            if (isDup) {
                Counter.increment(dupRef)
            } else ();
            Ref.put(Some(curr), prevRef);
            Counter.increment(sizeRef)
        });
        let size = Counter.peek(sizeRef);
        let dup = Counter.peek(dupRef);
        size / (size - dup)

}