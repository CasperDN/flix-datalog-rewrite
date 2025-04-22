mod Fixpoint.Phase.JoinOptimizer {
    use Fixpoint.Ram.{RamProgram, RamStmt}
    use Fixpoint.Phase.JoinProfiler
    use Fixpoint.Phase.JoinProfiler.JoinProfile
    
    def costToJoin(relations: Vector[RowVar], s: RowVar): (Int32, List[RowVar]) = 
        let (cost, _) = 

    def scheduleProgram(program: RamProgram): RamProgram = match program {
        case RamProgram.Program(stmt, facts, predState, indexInfo) => 
            match JoinProfiler.profileProgram(program) {
                case JoinProfile.Profile(sizePerIter, attrToSize) => 

                    ???
            }
    }

    def scheduleStmt(stmt: RamStmt): RamStmt = match program {
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

    def scheduleOp(op: RelOp): RelOp = match program {
        case Search(rowVar, relSym, body) => ???
        case Query(rowVar, relSym, boolExps, _, body) => ???
        case Functional(_, _, _, body, _) => scheduleOp(body)
        case Project(_, _) => op
        case If(_, body) => scheduleOp(body)
    }


}