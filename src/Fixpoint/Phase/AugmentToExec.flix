mod Fixpoint.Phase.AugmentToExec {
    use Fixpoint.Interpreter.Database
    use Fixpoint.Normalization.ObjectMarshallingInfo;
    use Fixpoint.Interpreter.DatabaseExternal
    use Fixpoint.Ast.AugmentedRam.getTermRamId
    use Fixpoint.Ast.AugmentedRam.RamId
    use Fixpoint.Ast.AugmentedRam.{TupleVar, RamStmt => ARamStmt, RelOp => ARelOp, RelSym, RamTerm => ARamTerm, BoolExp => ABoolExp, TupleVar => ATupleVar}
    use Fixpoint.Ast.AugmentedRam.RelOp.{Search => ASearch, SearchWithIndex => ASearchWithIndex, Functional => AFunctional, Project => AProject, If => AIf}
    use Fixpoint.Ast.AugmentedRam.BoolExp.{IsEmpty => AIsEmpty, NotMemberOf => ANotMemberOf, Eq => AEq, Leq => ALeq, Guard0 => AGuard0, Guard1 => AGuard1, Guard2 => AGuard2, Guard3 => AGuard3, Guard4 => AGuard4, Guard5 => AGuard5}
    use Fixpoint.Ast.AugmentedRam.RamTerm.{Lit => ALit, RowLoad => ARowLoad, Meet => AMeet, App0 => AApp0, App1 => AApp1, App2 => AApp2, App3 => AApp3, App4 => AApp4, App5 => AApp5}


    use Fixpoint.Ast.ExecutableRam.{RamStmt => ERamStmt, RelOp => ERelOp, RamTerm => ERamTerm, BoolExp => EBoolExp, TupleVar => ETupleVar}
    use Fixpoint.Ast.ExecutableRam.RelOp.{Search => ESearch, SearchWithIndex => ESearchWithIndex, Functional => EFunctional, Project => EProject, If => EIf}
    use Fixpoint.Ast.ExecutableRam.BoolExp.{IsEmpty => EIsEmpty, NotMemberOf => ENotMemberOf, Eq => EEq, Leq => ELeq, Guard0 => EGuard0, Guard1 => EGuard1, Guard2 => EGuard2, Guard3 => EGuard3, Guard4 => EGuard4, Guard5 => EGuard5}
    use Fixpoint.Ast.ExecutableRam.RamTerm.{Lit => ELit, LoadIndex => ELoadIndex, Meet => EMeet, App0 => EApp0, App1 => EApp1, App2 => EApp2, App3 => EApp3, App4 => EApp4, App5 => EApp5}

    use Fixpoint.Ast.AugmentedRam.AugmentedProgram
    use Fixpoint.Ast.AugmentedRam
    use Fixpoint.Ast.ExecutableRam.RamProgram

    use Fixpoint.Normalization.Equality
    use Fixpoint.Normalization

    use Fixpoint.Counter
    use Fixpoint.Counter.Counter

    type alias IdToIndex[r: Eff] = MutMap[RamId, Int32, r]

    @Internal
    pub def compileToExec(rc: Region[r], db: DatabaseExternal[r], program: AugmentedProgram): (RamProgram, Database[r], ObjectMarshallingInfo[r]) \ r = match program { 
        case AugmentedProgram.Program(stmt, facts, meta, _) =>
            let counter = Counter.empty(rc);
            let idToIndex = MutMap.empty(rc);
            // let f = Normalization.initialize();
            let ramIDToNormalIndex = Equality.computeMapping(program);
            let compiledStmt = compileStmt(stmt, counter, idToIndex);
            // Compile facts.
            (RamProgram.Program(compiledStmt, ???, meta, ???), ???, ???)
    }

    @Internal
    pub def compileStmt(stmt: ARamStmt, counter: Counter[r1], idToIndex: IdToIndex[r2]): ERamStmt \ {r1, r2} = region rc {
        let recurse = x -> compileStmt(x, counter, idToIndex);
        let recurseNewCount = x -> compileStmt(x, Counter.clone(counter, rc), idToIndex);
        match stmt {
        case ARamStmt.Insert(op) =>
            let newOp = compileOp(op, rc, counter, idToIndex);
            ERamStmt.Insert(newOp)
            // if(MutList.size(independent) == 0) 
            //     ERamStmt.Insert(newOp) else ERamStmt.Insert(EIf(MutList.toVector(independent), newOp))
        case ARamStmt.Seq(xs) => Vector.map(x -> compileStmt(x, Counter.clone(counter, rc), idToIndex), xs) |> ERamStmt.Seq
        case ARamStmt.Par(xs) => Vector.map(x -> compileStmt(x, Counter.clone(counter, rc), idToIndex), xs) |> ERamStmt.Par
        case ARamStmt.Until(test, body) => ERamStmt.Until(Vector.map(x -> compileBool(x, counter, idToIndex), test), compileStmt(body, counter, idToIndex))

        case ARamStmt.Merge(s1, s2) => ERamStmt.Merge(s1, s2, ???)
        case ARamStmt.Swap(s1, s2) => ERamStmt.Swap(s1, s2)
        case ARamStmt.Purge(s) => ERamStmt.Purge(s)
        case ARamStmt.Comment(s) => ERamStmt.Comment(s)
    }}

    @Internal
    def compileOp(op: ARelOp, rc: Region[r], counter: Counter[r1], idToIndex: IdToIndex[r2]): ERelOp \ {r, r1, r2} = 
        let recursiveCall: ARelOp -> ERelOp \ {r, r1, r2} = x -> compileOp(x, rc, counter, idToIndex);
        match op {
        // We could here keep the BoolExps that we do not want to handle as if, but then we limit later iterations of the query algorithms, or require that this file is changed later
            case ASearch(tpv, relSym, rest) =>
                let arity = AugmentedRam.arityOf(relSym);
                let ATupleVar.Named(id) = tpv;
                let _ = Vector.forEach(x -> MutMap.put(RamId.TuplePos(id, x), Counter.getNewID(counter), idToIndex), Vector.range(0, arity));
                ESearch(compileTupleVar(tpv), relSym, recursiveCall(rest))
            case AFunctional(tpv, f, terms, rest, _arity) => EFunctional(compileTupleVar(tpv), f, Vector.map(x -> compileTerm(x, counter, idToIndex), terms), recursiveCall(rest), ???) // TODO: Fix intToBox
            case AProject(terms, s) => EProject(Vector.map(x -> compileTerm(x, counter, idToIndex), terms), s, ???)
            case AIf(boolExps, rest) =>
                EIf(Vector.map(x -> compileBool(x, counter, idToIndex), boolExps), recursiveCall(rest))
            case ASearchWithIndex(tpv, relSym, tests, rest) => 
                let compiledTests = Vector.map(x -> compileBool(x, counter, idToIndex), tests);
                ESearchWithIndex(compileTupleVar(tpv), relSym, compiledTests, recursiveCall(rest))
        }

    @Internal
    def compileTerm(term: ARamTerm, counter: Counter[r1], mapToIndex: IdToIndex[r2]): ERamTerm \ {r1, r2} =
        let compileT = x -> compileTerm(x, counter, mapToIndex);
        let getI = x -> getIndex(x, counter, mapToIndex);
        match term {
            case ALit(val, id)                      => ELit(???)
            case ARowLoad(_, _, _)                  => ELoadIndex(unwrap(MutMap.get(getTermRamId(term), mapToIndex)))
            // case ALoadLatVar(_, _, id)              => ELoadIndex(unwrap(MutMap.get(id, mapToIndex)))
            case AMeet(f, t1, t2, id)               => EMeet(f, compileT(t1), compileT(t1), ???)
            case AApp0(f, id)                       => EApp0(f, getI(id))
            case AApp1(f, t1, id)                   => EApp1(f, compileT(t1), getI(id), ???)
            case AApp2(f, t1, t2, id)               => EApp2(f, compileT(t1), compileT(t2), getI(id), ???, ???)
            case AApp3(f, t1, t2, t3, id)           => EApp3(f, compileT(t1), compileT(t2), compileT(t3), getI(id), ???, ???, ???)
            case AApp4(f, t1, t2, t3, t4, id)       => EApp4(f, compileT(t1), compileT(t2), compileT(t3), compileT(t4), getI(id), ???, ???, ???, ???)
            case AApp5(f, t1, t2, t3, t4, t5, id)   => EApp5(f, compileT(t1), compileT(t2), compileT(t3), compileT(t4), compileT(t5), getI(id), ???, ???, ???, ???, ???)
    }

    @Internal
    def compileBool(bool: ABoolExp, counter: Counter[r1], map: IdToIndex[r2]): EBoolExp \ {r1, r2} = 
        let compileT = x -> compileTerm(x, counter, map);
        match bool {
            case AIsEmpty(s) => EIsEmpty(s)
            case ANotMemberOf(terms, s) => ENotMemberOf(Vector.map(compileT, terms), s, ???)
            case AEq(term1, term2) => EEq(compileT(term1), compileT(term2))
            case ALeq(f, term1, term2) => ELeq(f, compileT(term1), compileT(term2), ???) // TODO: Fix intToBox
            case AGuard0(f) => EGuard0(f)
            case AGuard1(f, term1) => EGuard1(f, compileT(term1), ???)
            case AGuard2(f, term1, term2) => EGuard2(f, compileT(term1), compileT(term2), ???, ???)
            case AGuard3(f, term1, term2, term3) => EGuard3(f, compileT(term1), compileT(term2), compileT(term3), ???, ???, ???)
            case AGuard4(f, term1, term2, term3, term4) => EGuard4(f, compileT(term1), compileT(term2), compileT(term3), compileT(term4), ???, ???, ???, ???)
            case AGuard5(f, term1, term2, term3, term4, term5) => EGuard5(f, compileT(term1), compileT(term2), compileT(term3), compileT(term4), compileT(term5), ???, ???, ???, ???, ???)
    }

    // @Internal
    // def compileRelSym(relSym: ARelSym): ERelSym = match relSym {
    //     case ARelSym.Symbol(p, i, d) => ERelSym.Symbol(p, i, d)
    // }

    @Internal
    def compileTupleVar(tupleVar: ATupleVar): ETupleVar = match tupleVar {
        case ATupleVar.Named(id) => ETupleVar.Named(id)
    }

    @Internal
    def getIndex(id: RamId, counter: Counter[r1], map: IdToIndex[r2]): Int32 \ {r1, r2} = match MutMap.get(id, map) {
        case Some(position) => position
        case None => 
            let position = Counter.getNewID(counter);
            MutMap.put(id, position, map);
            position
    }

    @Internal
    def unwrap(opt: Option[a]): a = match opt {
        case None => ???
        case Some(v) => v
    }


}