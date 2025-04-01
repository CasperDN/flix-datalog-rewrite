mod Fixpoint.Phase.AugmentToExec {
    use Fixpoint.Interpreter.Database
    use Fixpoint.Normalization.Normalization;
    use Fixpoint.Interpreter.DatabaseExternal
    use Fixpoint.Ast.Ram.{RamProgram => AProgram, getTermRamId, RamId}
    use Fixpoint.Ast.Ram.{TupleVar, RamStmt => ARamStmt, RelOp => ARelOp, RelSym, RamTerm => ARamTerm, BoolExp => ABoolExp, TupleVar => ATupleVar}
    use Fixpoint.Ast.Ram.RelOp.{Search => ASearch, SearchWithIndex => ASearchWithIndex, Functional => AFunctional, Project => AProject, If => AIf}
    use Fixpoint.Ast.Ram.BoolExp.{IsEmpty => AIsEmpty, NotMemberOf => ANotMemberOf, Eq => AEq, Leq => ALeq, Guard0 => AGuard0, Guard1 => AGuard1, Guard2 => AGuard2, Guard3 => AGuard3, Guard4 => AGuard4, Guard5 => AGuard5}
    use Fixpoint.Ast.Ram.RamTerm.{Lit => ALit, RowLoad => ARowLoad, Meet => AMeet, App0 => AApp0, App1 => AApp1, App2 => AApp2, App3 => AApp3, App4 => AApp4, App5 => AApp5}


    use Fixpoint.Ast.ExecutableRam.{RamStmt => ERamStmt, RelOp => ERelOp, RamTerm => ERamTerm, BoolExp => EBoolExp}
    use Fixpoint.Ast.ExecutableRam.RelOp.{Search => ESearch, SearchWithIndex => ESearchWithIndex, Functional => EFunctional, Project => EProject, If => EIf}
    use Fixpoint.Ast.ExecutableRam.BoolExp.{IsEmpty => EIsEmpty, NotMemberOf => ENotMemberOf, Eq => EEq, Leq => ELeq, Guard0 => EGuard0, Guard1 => EGuard1, Guard2 => EGuard2, Guard3 => EGuard3, Guard4 => EGuard4, Guard5 => EGuard5}
    use Fixpoint.Ast.ExecutableRam.RamTerm.{Lit => ELit, LoadIndex => ELoadIndex, Meet => EMeet, App0 => EApp0, App1 => EApp1, App2 => EApp2, App3 => EApp3, App4 => EApp4, App5 => EApp5}

    use Fixpoint.Ast.Ram
    use Fixpoint.Ast.ExecutableRam.{RamProgram => EProgram}

    use Fixpoint.Ast.Shared.{Denotation, PredSym}

    use Fixpoint.Normalization.{Equality, RamIdToMarshal}
    use Fixpoint.Normalization

    use Fixpoint.Counter
    use Fixpoint.Counter.Counter

    type alias IdToIndex[r: Eff] = MutMap[RamId, Int32, r]

    def relSymToDenId(relSym: RelSym, idToMarshall: RamIdToMarshal): Int32 = match relSym {
                case RelSym.Symbol(_, _, Denotation.Relational) => -1
                case RelSym.Symbol(PredSym.PredSym(_, id), arity, Denotation.Latticenal(_, _, _, _)) =>
                    unwrap(Map.get(RamId.RelPos(id, arity), idToMarshall))
            }

    @Internal
    pub def compileToExec(rc: Region[r], program: AProgram): (EProgram, Normalization[r]) \ r = match program { 
        case AProgram.Program(stmt, facts, meta, indexInfo) =>
            unchecked_cast(println("Hej") as _ \ r);
            let counter = Counter.empty(rc);
            let idToIndex = MutMap.empty(rc);
            let (marshall, idToMarshall) = Normalization.initialize(rc, program);
            unchecked_cast(println("Hej3") as _ \ r);
            unchecked_cast(println("Hej4") as _ \ r);
            let compiledStmt = compileStmt(stmt, counter, idToIndex, idToMarshall, marshall);
            unchecked_cast(println("Hej5") as _ \ r);
            let newFacts = Map.mapWithKey(k -> values ->
                let RelSym.Symbol(PredSym.PredSym(_, id), _, _) = k;
                Vector.map(vec ->
                    Vector.mapWithIndex(index -> v ->
                        Normalization.normalizeBox(v, unwrap(Map.get(RamId.RelPos(id, index), idToMarshall)))
                    , vec)
                , values)
            );
            // Compile facts.
            (EProgram.Program(compiledStmt, newFacts, meta, indexInfo), marshall)
    }

    @Internal
    def compileStmt(stmt: ARamStmt, counter: Counter[r1], idToIndex: IdToIndex[r2], idToMarshall: RamIdToMarshal, marshall: Normalization[r]): ERamStmt \ {r1, r2, r} = region rc {
        let recurse = x -> compileStmt(x, counter, idToIndex, idToMarshall, marshall);
        let recurseNewCount = x -> compileStmt(x, Counter.clone(counter, rc), idToIndex, idToMarshall, marshall);
        match stmt {
        case ARamStmt.Insert(op) =>
            let newOp = compileOp(op, rc, counter, idToIndex, idToMarshall, marshall);
            ERamStmt.Insert(newOp)
            // if(MutList.size(independent) == 0) 
            //     ERamStmt.Insert(newOp) else ERamStmt.Insert(EIf(MutList.toVector(independent), newOp))
        case ARamStmt.Seq(xs) => Vector.map(x -> recurseNewCount(x), xs) |> ERamStmt.Seq
        case ARamStmt.Par(xs) => Vector.map(x -> recurseNewCount(x), xs) |> ERamStmt.Par
        case ARamStmt.Until(test, body) => ERamStmt.Until(Vector.map(x -> compileBool(x, counter, idToIndex, idToMarshall, marshall), test), recurse(body))

        case ARamStmt.Merge(s1, s2) => ERamStmt.Merge(s1, s2, relSymToDenId(s1, idToMarshall))
        case ARamStmt.Swap(s1, s2) => ERamStmt.Swap(s1, s2)
        case ARamStmt.Purge(s) => ERamStmt.Purge(s)
        case ARamStmt.Comment(s) => ERamStmt.Comment(s)
    }}

    @Internal
    def compileOp(op: ARelOp, rc: Region[r], counter: Counter[r1], idToIndex: IdToIndex[r2], idToMarshall: RamIdToMarshal, marshall: Normalization[r3]): ERelOp \ {r, r1, r2, r3} = 
        let recursiveCall: ARelOp -> ERelOp \ {r, r1, r2, r3} = x -> compileOp(x, rc, counter, idToIndex, idToMarshall, marshall);
        match op {
        // We could here keep the BoolExps that we do not want to handle as if, but then we limit later iterations of the query algorithms, or require that this file is changed later
            case ASearch(tpv, relSym, rest) =>
                let arity = Ram.arityOf(relSym);
                let ATupleVar.Named(id) = tpv;
                let _ = Vector.forEach(x -> MutMap.put(RamId.TuplePos(id, x), Counter.getNewID(counter), idToIndex), Vector.range(0, arity));
                ESearch(compileTupleVar(tpv), relSym, recursiveCall(rest))
            case AFunctional(tpv, f, terms, rest, arity) =>
                let TupleVar.Named(id) = tpv;
                let termToIndex = term -> unwrap(Map.get(getTermRamId(term), idToMarshall));
                let idToMarhsalled = id_ -> unwrap(Map.get(id_, idToMarshall));
                let from_ = Vector.map(termToIndex, terms);
                let to = Vector.map(i -> idToMarhsalled(RamId.TuplePos(id, i)), Vector.range(0, arity));
                EFunctional(compileTupleVar(tpv), f, Vector.map(x -> compileTerm(x, counter, idToIndex, idToMarshall, marshall), terms), recursiveCall(rest), from_, to)
            case AProject(terms, s) => EProject(Vector.map(x -> compileTerm(x, counter, idToIndex, idToMarshall, marshall), terms), s, relSymToDenId(s, idToMarshall))
            case AIf(boolExps, rest) =>
                EIf(Vector.map(x -> compileBool(x, counter, idToIndex, idToMarshall, marshall), boolExps), recursiveCall(rest))
            case ASearchWithIndex(tpv, relSym, tests, index, rest) => 
                let compiledTests = Vector.map(x -> compileBool(x, counter, idToIndex, idToMarshall, marshall), tests);
                ESearchWithIndex(compileTupleVar(tpv), relSym, compiledTests, index, recursiveCall(rest))
            // case _ => ???
        }

    @Internal
    def compileTerm(term: ARamTerm, counter: Counter[r1], mapToIndex: IdToIndex[r2], idToMarshall: RamIdToMarshal, marshall: Normalization[r]): ERamTerm \ {r, r1, r2} =
        let compileT = x -> compileTerm(x, counter, mapToIndex, idToMarshall, marshall);
        let termToIndex = term1 -> unwrap(Map.get(getTermRamId(term1), idToMarshall));
        let termToM = t -> unwrap(Map.get(getTermRamId(t), idToMarshall));
        let idToMarhsalled = id -> unwrap(Map.get(id, idToMarshall));
        match term {
            case ALit(val, id)                      => ELit(Normalization.normalizeBox(val, unwrap(Map.get(id, idToMarshall)), marshall))
            case ARowLoad(_, _, _)                  => ELoadIndex(unwrap(MutMap.get(getTermRamId(term), mapToIndex)))
            case AMeet(f, t1, t2, _)               =>  EMeet(f, compileT(t1), compileT(t2), termToM(t1))
            case AApp0(f, id)                       => EApp0(f, idToMarhsalled(id))
            case AApp1(f, t1, id)                   => EApp1(f, compileT(t1), termToM(t1), idToMarhsalled(id))
            case AApp2(f, t1, t2, id)               => EApp2(f, compileT(t1), compileT(t2), termToM(t1), termToM(t2), idToMarhsalled(id))
            case AApp3(f, t1, t2, t3, id)           => EApp3(f, compileT(t1), compileT(t2), compileT(t3), termToM(t1), termToM(t2), termToM(t3), idToMarhsalled(id))
            case AApp4(f, t1, t2, t3, t4, id)       => EApp4(f, compileT(t1), compileT(t2), compileT(t3), compileT(t4), termToM(t1), termToM(t2), termToIndex(t3), termToM(t4), idToMarhsalled(id))
            case AApp5(f, t1, t2, t3, t4, t5, id)   => EApp5(f, compileT(t1), compileT(t2), compileT(t3), compileT(t4), compileT(t5), termToM(t1), termToM(t2), termToM(t3), termToM(t4), termToM(t5), idToMarhsalled(id))
            case _ => ELit(0i64)
    }

    @Internal
    def compileBool(bool: ABoolExp, counter: Counter[r1], map: IdToIndex[r2], idToMarshall: RamIdToMarshal, marshall: Normalization[r]): EBoolExp \ {r, r1, r2} = 
        let termToIndex = term -> unwrap(Map.get(getTermRamId(term), idToMarshall));
        let compileT = x -> compileTerm(x, counter, map, idToMarshall, marshall);
        match bool {
            case AIsEmpty(s) => EIsEmpty(s)
            case ANotMemberOf(terms, s) => ENotMemberOf(Vector.map(compileT, terms), s, relSymToDenId(s, idToMarshall))
            case AEq(term1, term2) => EEq(compileT(term1), compileT(term2))
            case ALeq(f, term1, term2) => ELeq(f, compileT(term1), compileT(term2), termToIndex(term1))
            case AGuard0(f) => EGuard0(f)
            case AGuard1(f, term1) => EGuard1(f, compileT(term1), termToIndex(term1))
            case AGuard2(f, term1, term2) => EGuard2(f, compileT(term1), compileT(term2), termToIndex(term1), termToIndex(term2))
            case AGuard3(f, term1, term2, term3) => EGuard3(f, compileT(term1), compileT(term2), compileT(term3), termToIndex(term1), termToIndex(term2), termToIndex(term3))
            case AGuard4(f, term1, term2, term3, term4) => EGuard4(f, compileT(term1), compileT(term2), compileT(term3), compileT(term4), termToIndex(term1), termToIndex(term2), termToIndex(term3), termToIndex(term4))
            case AGuard5(f, term1, term2, term3, term4, term5) => EGuard5(f, compileT(term1), compileT(term2), compileT(term3), compileT(term4), compileT(term5), termToIndex(term1), termToIndex(term2), termToIndex(term3), termToIndex(term4), termToIndex(term5))
    }

    @Internal
    def compileTupleVar(tupleVar: ATupleVar): Int32 = match tupleVar {
        case ATupleVar.Named(id) => id
    }

    // @Internal
    // def getIndex(id: RamId, counter: Counter[r1], map: IdToIndex[r2]): Int32 \ {r1, r2} = match MutMap.get(id, map) {
    //     case Some(position) => position
    //     case None => 
    //         let position = Counter.getNewID(counter);
    //         MutMap.put(id, position, map);
    //         position
    // }

    @Internal
    def unwrap(opt: Option[a]): a = match opt {
        case None => bug!("Unwrap none in AugmentToExec")
        case Some(v) => v
    }


}