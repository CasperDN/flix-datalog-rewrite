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
    
    def costToJoin(relations: Vector[RowVar], s: RowVar): (Int32, List[RowVar]) = 
        let (cost, _) = ???;
        ???

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