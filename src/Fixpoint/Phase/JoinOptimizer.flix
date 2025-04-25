/**
How should functional be handled?
Simple: For every input they are called with record it. The estimated size of a join is then the average size
over the seen values. Like everything else this relies somewhat on a uniformity assumption which is likely
to not be true in practice, but it is better than nothing.

Join algorithm should be Selinger's algorithm. Cost computed as on page 12.
Important note: When joining with a functional the cost is infinity if one of inputs
have yet to be computed. In practice return a None or something like that to avoid errors
leading to choosing an unsound join order.

*/


mod Fixpoint.Phase.JoinOptimizer {
    use Fixpoint.Ast.Ram.{RamProgram, RamStmt, RowVar, RelOp}
    use Fixpoint.Phase.JoinProfiler
    use Fixpoint.Phase.JoinProfiler.JoinProfile
    use Fixpoint.Helpers.unwrap


    def costToJoin(
        relations: List[RowVar], 
        optimal: MutMap[List[RowVar], (Int64, List[RowVar]), r], 
        tuplesFromJoin: MutMap[List[RowVar], Vector[Int64], r],
        expectedJoinSize: Map[(RowVar, Vector[Int32]), Vector[Int64]],
        attributeMap: Map[RowVar, Map[RowVar, Set[Int32]]],
        arity: Int64,
        s: RowVar
    ): Int64 \ r =
        let map = Map.get(s, attributeMap) |> unwrap;
        // Requires that Set orders its elements
        let attr = 
            relations |> 
            List.foldLeft(acc -> rel -> Set.union(acc, Map.get(rel, map) |> unwrap), Set#{}) |>
            Set.toList |>
            List.toVector;
        let (costToJoinPrev, _) = MutMap.get(relations, optimal) |> unwrap;
        let sum = 
            Vector.zip(
                MutMap.get(relations, tuplesFromJoin) |> unwrap, 
                Map.get((s, attr), expectedJoinSize) |> unwrap
            ) |>
            Vector.foldLeft(acc -> match (x, y) -> acc + x * y, 0i64);
        costToJoinPrev + arity * sum
    
    def powerSetOfSize(size: Int32): List[List[RowVar]] = ???

    def getOptimalJoin(relations: List[RowVar], profile: JoinProfile): List[RowVar] = match profile {
        case JoinProfile.Profile(_, _) => region rc {
            let optimal: MutMap[List[RowVar], (Int64, List[RowVar]), rc] = MutMap.empty(rc);
            List.forEach(rel -> MutMap.put(rel :: Nil, (0i64, rel :: Nil), optimal), relations);
            let max = List.length(relations);
            def loop(num) = {
                if (num >= max) ()
                else {
                    powerSetOfSize(num) |>
                    List.forEach(s -> {
                        let opt = s |> List.mapWithIndex(i -> attr -> {
                            let (ls, right) = List.splitAt(i, s);
                            let rs = List.drop(1, right);
                            let withoutAttr = ls ::: rs;
                            let prevJoin = snd(MutMap.get(withoutAttr, optimal) |> unwrap);
                            let optJoin = attr :: prevJoin;
                            (costToJoin(withoutAttr, optimal, ???, ???, ???, ???, attr), optJoin)
                        }) |> List.minimumBy(x -> y -> fst(x) <=> fst(y)) |> unwrap;
                        MutMap.put(s, opt, optimal)
                    });
                    loop(num + 1)
                }
            };
            loop(2);
            MutMap.get(relations, optimal) |> unwrap |> snd
        }
    }

    def scheduleProgram(program: RamProgram): RamProgram = match program {
        case RamProgram.Program(stmt, facts, predState, indexInfo) => 
            match JoinProfiler.profileProgram(program) {
                case JoinProfile.Profile(sizePerIter, attrToSize) => 

                    ???
            }
    }

    def scheduleStmt(stmt: RamStmt): RamStmt = match stmt {
        case RamStmt.Insert(op) => RamStmt.Insert(scheduleOp(op))
        case RamStmt.Merge(_, _) => stmt
        case RamStmt.Swap(_, _) => stmt
        case RamStmt.Purge(_) => stmt
        case RamStmt.Seq(xs) => RamStmt.Seq(Vector.map(scheduleStmt, xs))
        case RamStmt.Par(xs) => RamStmt.Par(Vector.map(scheduleStmt, xs))
        case RamStmt.Until(boolExps, body) => RamStmt.Until(boolExps, scheduleStmt(body))
        case RamStmt.Comment(_) => stmt
        case RamStmt.EstimateJoinSize(_, _, _, _) => unreachable!()
    }

    def scheduleOp(op: RelOp): RelOp = match op {
        case RelOp.Search(rowVar, relSym, body) => ???
        case RelOp.Query(rowVar, relSym, boolExps, _, body) => ???
        case RelOp.Functional(_, _, _, body, _) => scheduleOp(body)
        case RelOp.Project(_, _) => op
        case RelOp.If(_, body) => scheduleOp(body)
    }


}