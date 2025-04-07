mod Fixpoint.Phase.AugmentToExec {
    use Fixpoint.Ast.Ram.IndexInformation
    use Fixpoint.Ast.Ram.Search
    use Fixpoint.UniqueInts
    use Fixpoint.Ast.ExecutableRam.WriteTuple
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
    use Fixpoint.Ast.ExecutableRam.RamTerm.{Lit => ELit, LoadIndex => ELoadIndex, Meet => EMeet, App0 => EApp0, App1 => EApp1, App2 => EApp2, App3 => EApp3, App4 => EApp4, App5 => EApp5, LoadFromTuple => ELoadFromTuple}

    use Fixpoint.Ast.Ram
    use Fixpoint.Ast.ExecutableRam.{RamProgram => EProgram}

    use Fixpoint.Ast.Shared.{Denotation, PredSym}

    use Fixpoint.Normalization.{Equality, RamIdToMarshal}
    use Fixpoint.Normalization

    use Fixpoint.Counter
    use Fixpoint.Counter.Counter

    // Maps TupleVars to their memory-position.
    type alias IdToIndex[r: Region] = UniqueInts.IndexState[TupleVar, r]

    type alias WriteTos[r: Region] = MutMap[TupleVar, List[WriteTuple], r]

    def relSymToDenId(relSym: RelSym, idToMarshall: RamIdToMarshal): Int32 = match relSym {
        case RelSym.Symbol(_, _, Denotation.Relational) => -1
        case RelSym.Symbol(PredSym.PredSym(_, id), arity, Denotation.Latticenal(_, _, _, _)) =>
            unwrap(Map.get(RamId.RelPos(id, arity), idToMarshall))
    }

    @Internal
    pub def compileToExec(rc: Region[r], program: AProgram): (EProgram, Normalization[r]) \ r = match program { 
        case AProgram.Program(stmt, facts, meta, indexInfo) =>
            unchecked_cast(println("Hej") as _ \ r);
            // let counter = Counter.empty(rc);
            let idToIndex = UniqueInts.empty(rc);
            let (marshall, idToMarshall) = Normalization.initialize(rc, program);
            unchecked_cast(println(Debug.stringify(idToMarshall)) as _ \ r);
            unchecked_cast(println("Hej3") as _ \ r);
            unchecked_cast(println("Hej4") as _ \ r);
            let writeTo = MutMap.empty(rc);
            let compiledStmt = compileStmt(stmt, rc, idToIndex, idToMarshall, marshall, writeTo, indexInfo);
            unchecked_cast(println("Hej5") as _ \ r);
            let newFacts = Map.mapWithKey(k -> values ->
                let RelSym.Symbol(PredSym.PredSym(_, id), _, _) = k;
                Vector.map(vec ->
                    Vector.mapWithIndex(index -> v ->
                        {unchecked_cast(println(id) as _ \ r);
                        let (_, _, back) = meta;
                        unchecked_cast(println(unwrap(Map.get(id, back))) as _ \ r);                        
                        unchecked_cast(println(index) as _ \ r);
                        Normalization.normalizeBox(v, unwrap(Map.get(RamId.RelPos(id, index), idToMarshall)), marshall)
                    }, vec)
                , values)
            , facts);
            // Compile facts.
            (EProgram.Program(compiledStmt, newFacts, meta, indexInfo, ???), marshall)
    }

    @Internal
    def compileStmt(stmt: ARamStmt, rc: Region[r], idToIndex: IdToIndex[r], idToMarshall: RamIdToMarshal, marshall: Normalization[r], writeTo: WriteTos[r], indexInfo: IndexInformation): ERamStmt \ r =
        let recurse = x -> compileStmt(x, rc, idToIndex, idToMarshall, marshall, writeTo, indexInfo);
        match stmt {
            case ARamStmt.Insert(op) =>
                let newOp = compileOp(op, rc, idToIndex, idToMarshall, marshall, writeTo, indexInfo);
                ERamStmt.Insert(newOp)
                // if(MutList.size(independent) == 0) 
                //     ERamStmt.Insert(newOp) else ERamStmt.Insert(EIf(MutList.toVector(independent), newOp))
            case ARamStmt.Seq(xs) => Vector.map(x -> recurse(x), xs) |> ERamStmt.Seq
            case ARamStmt.Par(xs) => Vector.map(x -> recurse(x), xs) |> ERamStmt.Par
            case ARamStmt.Until(test, body) => ERamStmt.Until(Vector.map(x -> compileBool(x, idToIndex, idToMarshall, marshall), test), recurse(body))

            // For all of these we have to do the operation for all indexes created for the relations.
            case ARamStmt.Merge(newRel, deltaRel) =>
                let (constructed, placements) = indexInfo;
                let newRelPos = unwrap(Map.get((newRel, 0), placements));
                let compileToMerge = index -> ERamStmt.Merge(newRelPos, index, relSymToDenId(deltaRel, idToMarshall));
                let deltaRels = Vector.length(unwrap(Map.get(deltaRel, constructed)));
                let merges = Vector.map(index -> compileToMerge(unwrap(Map.get((deltaRel, index), placements))), Vector.range(1, deltaRels));
                if(Vector.length(merges) == 1) {
                    Vector.get(0, merges)
                } else {
                    ERamStmt.Par(merges)
                }
            case ARamStmt.Swap(newRel, deltaRel) => 
                let (constructed, placements) = indexInfo;
                let newRelPos = unwrap(Map.get((newRel, 0), placements));
                let compileToMerge = index -> ERamStmt.Merge(newRelPos, index, relSymToDenId(deltaRel, idToMarshall));
                let deltaRels = Vector.length(unwrap(Map.get(deltaRel, constructed)));
                let swapPart = ERamStmt.Swap(newRelPos, unwrap(Map.get((deltaRel, 0), placements)));
                if (deltaRels == 1) {
                    swapPart
                } else {
                    let merges = Vector.map(index -> compileToMerge(unwrap(Map.get((deltaRel, index), placements))), Vector.range(1, deltaRels));
                    if(Vector.length(merges) == 1) {
                        ERamStmt.Seq(Vector#{Vector.get(0, merges), swapPart})
                    } else {
                        ERamStmt.Seq(Vector#{ERamStmt.Par(merges), swapPart})
                    }
                }
            case ARamStmt.Purge(s) =>
                let (constructed, placements) = indexInfo;
                let indexNums = Vector.range(0, Vector.length(unwrap(Map.get(s, constructed))));
                let purges = Vector.map(i -> ERamStmt.Purge(unwrap(Map.get((s, i), placements))), indexNums);
                if (Vector.length(purges) == 1) {
                    Vector.get(0, purges)
                } else {
                    ERamStmt.Seq(purges)
                }
            case ARamStmt.Comment(s) => ERamStmt.Comment(s)
    }

    @Internal
    def compileOp(op: ARelOp, rc: Region[r], idToIndex: IdToIndex[r], idToMarshall: RamIdToMarshal, marshall: Normalization[r], writeTo: WriteTos[r], indexInfo: IndexInformation): ERelOp \ r = 
        let recursiveCall: ARelOp -> ERelOp \ r = x -> compileOp(x, rc, idToIndex, idToMarshall, marshall, writeTo, indexInfo);
        match op {
            case ASearch(tpv, relSym, body) =>
                // let arity = Ram.arityOf(relSym);
                // let ATupleVar.Named(id) = tpv;
                // let _ = Vector.forEach(x -> MutMap.put(RamId.TuplePos(id, x), Counter.getNewID(counter), idToIndex), Vector.range(0, arity));
                // let thisPosition = UniqueInts.getIndex(tpv, idToIndex);
                let compiledBody = recursiveCall(body);
                let thisWriteTo = getWriteTo(tpv, writeTo);
                let placements = snd(indexInfo);
                let relPos = unwrap(Map.get((relSym, 0), placements));
                ESearch(compileTupleVar(tpv), relPos, thisWriteTo, compiledBody)
            case AFunctional(tpv, f, terms, body, arity) =>
                let TupleVar.Named(id) = tpv;
                let termToIndex = term -> unwrap(Map.get(getTermRamId(term), idToMarshall));
                let idToMarhsalled = id_ -> unwrap(Map.get(id_, idToMarshall));
                let from_ = Vector.map(termToIndex, terms);
                // let thisPosition = UniqueInts.getIndex(tpv, idToIndex);
                let compiledBody = recursiveCall(body);
                let thisWriteTo = getWriteTo(tpv, writeTo);
                let to = Vector.map(i -> idToMarhsalled(RamId.TuplePos(id, i)), Vector.range(0, arity));
                EFunctional(compileTupleVar(tpv), f, Vector.map(x -> compileTerm(x, idToIndex, idToMarshall, marshall), terms), thisWriteTo, compiledBody, from_, to)
            case AProject(terms, s) => EProject(Vector.map(x -> compileTerm(x, idToIndex, idToMarshall, marshall), terms), s, relSymToDenId(s, idToMarshall))
            case AIf(boolExps, body) =>
                EIf(Vector.map(x -> compileBool(x, idToIndex, idToMarshall, marshall), boolExps), recursiveCall(body))
            case ASearchWithIndex(tpv, _, tests, index, body) =>
                let compiledTests = Vector.map(x -> compileBool(x, idToIndex, idToMarshall, marshall), tests);
                // Remove the bools that are used for the index anyway.
                Vector.filterMap(x -> match x {
                    case ABoolExp.Eq(ARamTerm.RowLoad(tpv1, index1, _), ARamTerm.RowLoad(tpv2, index2, _)) if tpv == tpv1 =>
                        let indexInSearch = ???;
                        addWriteTo(tpv2, index2, tpv1, indexInSearch, writeTo);
                        None
                    case ABoolExp.Eq(ARamTerm.RowLoad(tpv2, index2, _), ARamTerm.RowLoad(tpv1, index1, _)) if tpv == tpv1 =>
                        let indexInSearch = ???;
                        addWriteTo(tpv2, index2, tpv1, indexInSearch, writeTo);
                        None
                    case _ => Some(x)
                }, tests);
                ESearchWithIndex(compileTupleVar(tpv), index, compiledTests, index, recursiveCall(body))
            // case _ => ???
        }

    def compileTerm(term: ARamTerm, mapToIndex: IdToIndex[r], idToMarshall: RamIdToMarshal, marshall: Normalization[r]): ERamTerm \ r =
        let compileT = x -> compileTerm(x, mapToIndex, idToMarshall, marshall);
        // let termToIndex = term1 -> unwrap(Map.get(getTermRamId(term1), idToMarshall));
        let termToM = t -> unwrap(Map.get(getTermRamId(t), idToMarshall));
        let idToMarhsalled = id -> unwrap(Map.get(id, idToMarshall));
        match term {
            case ALit(val, id)                      => ELit(Normalization.normalizeBox(val, unwrap(Map.get(id, idToMarshall)), marshall))
            case ARowLoad(tpv, index, _)            => ELoadFromTuple(UniqueInts.getIndex(tpv, mapToIndex), index)
            case AMeet(f, t1, t2, _)                => EMeet(f, compileT(t1), compileT(t2), termToM(t1))
            case AApp0(f, id)                       => EApp0(f, idToMarhsalled(id))
            case AApp1(f, t1, id)                   => EApp1(f, compileT(t1), termToM(t1), idToMarhsalled(id))
            case AApp2(f, t1, t2, id)               => EApp2(f, compileT(t1), compileT(t2), termToM(t1), termToM(t2), idToMarhsalled(id))
            case AApp3(f, t1, t2, t3, id)           => EApp3(f, compileT(t1), compileT(t2), compileT(t3), termToM(t1), termToM(t2), termToM(t3), idToMarhsalled(id))
            case AApp4(f, t1, t2, t3, t4, id)       => EApp4(f, compileT(t1), compileT(t2), compileT(t3), compileT(t4), termToM(t1), termToM(t2), termToM(t3), termToM(t4), idToMarhsalled(id))
            case AApp5(f, t1, t2, t3, t4, t5, id)   => EApp5(f, compileT(t1), compileT(t2), compileT(t3), compileT(t4), compileT(t5), termToM(t1), termToM(t2), termToM(t3), termToM(t4), termToM(t5), idToMarhsalled(id))
            case _ => ELit(0i64)
    }

    def compileBool(bool: ABoolExp, map: IdToIndex[r], idToMarshall: RamIdToMarshal, marshall: Normalization[r]): EBoolExp \ r = 
        let termToIndex = term -> unwrap(Map.get(getTermRamId(term), idToMarshall));
        let compileT = x -> compileTerm(x, map, idToMarshall, marshall);
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

    def compileTupleVar(tupleVar: ATupleVar): Int32 = match tupleVar {
        case ATupleVar.Named(id) => id
    }

    def getWriteTo(tupleVar: ATupleVar, writeTo: WriteTos[r]): Vector[WriteTuple] \ r = 
        List.toVector(Option.getWithDefault(Nil, MutMap.get(tupleVar, writeTo)))

    def addWriteTo(fromTuple: ATupleVar, fromIndex: Int32, toTuple: ATupleVar, toIndex: Int32, writeTo: WriteTos[r]): Unit \ r =
        let written = (fromIndex, compileTupleVar(toTuple), toIndex);
        MutMap.putWith(_ -> old -> written :: old, fromTuple, written :: Nil, writeTo)


    def unwrap(opt: Option[a]): a = match opt {
        case None => bug!("Unwrap none in AugmentToExec")
        case Some(v) => v
    }


}