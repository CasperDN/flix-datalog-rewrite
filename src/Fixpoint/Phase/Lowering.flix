mod Fixpoint.Phase.Lowering {
    use Fixpoint.Boxed.BoxedBool
    use Fixpoint.Ast.Ram.IndexInformation
    use Fixpoint.Ast.Ram.Search
    use Fixpoint.UniqueInts
    use Fixpoint.Ast.ExecutableRam.WriteTuple
    use Fixpoint.Interpreter.Database
    use Fixpoint.Boxing.Boxing;
    use Fixpoint.Interpreter.DatabaseExternal
    use Fixpoint.Ast.Ram.{RamProgram => AProgram, getTermRamId, RamId, toDenotation}
    use Fixpoint.Ast.Ram.{RowVar, RamStmt => ARamStmt, RelOp => ARelOp, RelSym, RamTerm => ARamTerm, BoolExp => ABoolExp}
    use Fixpoint.Ast.Ram.RelOp.{Search => ASearch, Query => AQuery, Functional => AFunctional, Project => AProject, If => AIf}
    use Fixpoint.Ast.Ram.BoolExp.{IsEmpty => AIsEmpty, NotMemberOf => ANotMemberOf, Eq => AEq, Guard0 => AGuard0, Guard1 => AGuard1, Guard2 => AGuard2, Guard3 => AGuard3, Guard4 => AGuard4, Guard5 => AGuard5}
    use Fixpoint.Ast.Ram.RamTerm.{Lit => ALit, RowLoad => ARowLoad, Meet => AMeet, App0 => AApp0, App1 => AApp1, App2 => AApp2, App3 => AApp3, App4 => AApp4, App5 => AApp5}


    use Fixpoint.Ast.ExecutableRam.{RamStmt => ERamStmt, RelOp => ERelOp, RamTerm => ERamTerm, BoolExp => EBoolExp}
    use Fixpoint.Ast.ExecutableRam.RelOp.{Search => ESearch, SearchLattice => ESearchLattice, Query => EQuery, Functional => EFunctional, Project => EProject, If => EIf}
    use Fixpoint.Ast.ExecutableRam.BoolExp.{IsEmpty => EIsEmpty, NotMemberOf => ENotMemberOf, Eq => EEq, Guard0 => EGuard0, Guard1 => EGuard1, Guard2 => EGuard2, Guard3 => EGuard3, Guard4 => EGuard4, Guard5 => EGuard5}
    use Fixpoint.Ast.ExecutableRam.RamTerm.{Lit => ELit, Meet => EMeet, App0 => EApp0, App1 => EApp1, App2 => EApp2, App3 => EApp3, App4 => EApp4, App5 => EApp5, LoadFromTuple => ELoadFromTuple, LoadLatVar => ELoadLatVar}

    use Fixpoint.Ast.Ram
    use Fixpoint.Ast.ExecutableRam.{RamProgram => EProgram}

    use Fixpoint.Ast.Shared.{Denotation, PredSym}

    use Fixpoint.Boxing.{Equality, RamIdToMarshal}
    use Fixpoint.Boxing
    use Fixpoint.Boxed
    use Fixpoint.Debugging

    use Fixpoint.Counter
    use Fixpoint.Counter.Counter

    // Maps RowVars to their memory-position.
    type alias IdToIndex[r: Region] = UniqueInts.IndexState[RowVar, r]

    type alias WriteTos[r: Region] = MutMap[RowVar, List[WriteTuple], r]

    def relSymToDenId(relSym: RelSym, idToMarshall: RamIdToMarshal): Int32 = match relSym {
        case RelSym.Symbol(_, _, Denotation.Relational) => -1
        case RelSym.Symbol(PredSym.PredSym(_, id), arity, Denotation.Latticenal(_, _, _, _)) =>
            unwrap(Map.get(RamId.RelPos(id, arity), idToMarshall))
    }

    @Internal
    pub def compileToExec(rc: Region[r], program: AProgram): (EProgram, Boxing[r]) \ r = match Debugging.notifyPreLowering(program) { 
        case AProgram.Program(stmt, facts, meta, indexInfo) =>
            // let counter = Counter.empty(rc);
            let idToIndex = UniqueInts.empty(rc);
            let (marshall, idToMarshall) = Boxing.initialize(rc, program);
            let writeTo = MutMap.empty(rc);
            let compiledStmt = compileStmt(stmt, rc, idToIndex, idToMarshall, marshall, writeTo, indexInfo);
            // Compile facts.
            let newFacts = 
                facts |>
                Map.mapWithKey(k -> values ->
                    let RelSym.Symbol(PredSym.PredSym(_, id), _, den) = k;
                    values |> 
                    Vector.map(vec -> match den {
                        case Denotation.Relational => 
                            let tuple = vec |>
                                Vector.mapWithIndex(i -> v -> 
                                    Boxing.debox(v, unwrap(Map.get(RamId.RelPos(id, i), idToMarshall)), marshall));
                            (tuple, Boxed.None)
                        case Denotation.Latticenal(_, _, _ ,_) =>
                            let len = Vector.length(vec);
                            let tuple = Array.empty(rc, len - 1);
                            vec |> Vector.forEachWithIndex(i -> term -> {
                                if (i < len)
                                    Array.put(Boxing.debox(term, unwrap(Map.get(RamId.RelPos(id, i), idToMarshall)), marshall), i, tuple)
                                else ()
                            });
                            let latVal = Vector.get(len - 1, vec);
                            (Array.toVector(tuple), latVal)
                            // let tuple = vec |>
                            //     Vector.mapWithIndex(i -> v -> Boxing.debox(v, unwrap(Map.get(RamId.RelPos(id, i), idToMarshall)), marshall));
                            // let (vec1, vec2) = Vector.splitAt(Vector.length(tuple) - 1, tuple);
                            // (vec1, Vector.get(0, vec2))
                    })
                );

            // Compute arities
            let arityInformation = Ram.collectTpvArity(program);
            let numOfArities = UniqueInts.peekCurrentId(idToIndex);
            let arities = Array.empty(rc, numOfArities);
            List.forEach(match (tpv, arity) -> 
                    Array.put(arity, UniqueInts.getIndex(tpv, idToIndex), arities)
            , arityInformation);
            (EProgram.Program(compiledStmt, newFacts, meta, indexInfo, Array.toVector(arities), idToMarshall), marshall)
    }

    @Internal
    def compileStmt(stmt: ARamStmt, rc: Region[r], idToIndex: IdToIndex[r], idToMarshall: RamIdToMarshal, marshall: Boxing[r], writeTo: WriteTos[r], indexInfo: IndexInformation): ERamStmt \ r =
        let compileStmtRec = x -> compileStmt(x, rc, idToIndex, idToMarshall, marshall, writeTo, indexInfo);
        match stmt {
            case ARamStmt.Insert(op) =>
                let newOp = compileOp(op, rc, idToIndex, idToMarshall, marshall, writeTo, indexInfo);
                ERamStmt.Insert(newOp)
                // if(MutList.size(independent) == 0) 
                //     ERamStmt.Insert(newOp) else ERamStmt.Insert(EIf(MutList.toVector(independent), newOp))
            case ARamStmt.Seq(xs) => Vector.map(x -> compileStmtRec(x), xs) |> ERamStmt.Seq
            case ARamStmt.Par(xs) => Vector.map(x -> compileStmtRec(x), xs) |> ERamStmt.Par
            case ARamStmt.Until(test, body) => ERamStmt.Until(Vector.map(x -> compileBool(x, idToIndex, idToMarshall, marshall, indexInfo), test), compileStmtRec(body))

            // For all of these we have to do the operation for all indexes created for the relations.
            case ARamStmt.Merge(newRel, deltaRel) =>
                let (constructed, placements) = indexInfo;
                let newRelPos = unwrap(Map.get((newRel, 0), placements));
                let lub = match toDenotation(newRel) {
                    case Denotation.Relational => _ -> _ -> bug!("Using lattice logic on normal relation")
                    case Denotation.Latticenal(_, _, lub, _) => lub
                };
                let compileToMerge = index -> ERamStmt.Merge(newRelPos, index, lub, relSymToDenId(deltaRel, idToMarshall));
                let deltaRels = Vector.length(unwrap(Map.get(deltaRel, constructed)));
                let merges = Vector.map(index -> compileToMerge(unwrap(Map.get((deltaRel, index), placements))), Vector.range(0, deltaRels));
                if(Vector.length(merges) == 1) {
                    Vector.get(0, merges)
                } else {
                    ERamStmt.Par(merges)
                }
            case ARamStmt.Swap(newRel, deltaRel) => 
                let (constructed, placements) = indexInfo;
                let newRelPos = unwrap(Map.get((newRel, 0), placements));
                let lub = match toDenotation(newRel) {
                    case Denotation.Relational => _ -> _ -> bug!("Using lattice logic on normal relation")
                    case Denotation.Latticenal(_, _, lub, _) => lub
                };
                let compileToMerge = index -> ERamStmt.Merge(newRelPos, index, lub, relSymToDenId(deltaRel, idToMarshall));
                let deltaRels = Vector.length(unwrap(Map.get(deltaRel, constructed)));
                let swapPart = ERamStmt.Swap(newRelPos, unwrap(Map.get((deltaRel, 0), placements)));
                if (deltaRels == 1) {
                    swapPart
                } else {
                    let merges = 
                        Vector.range(1, deltaRels) |>
                        Vector.map(index -> compileToMerge(unwrap(Map.get((deltaRel, index), placements))));
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
    def compileOp(op: ARelOp, rc: Region[r], idToIndex: IdToIndex[r], idToMarshall: RamIdToMarshal, marshall: Boxing[r], writeTo: WriteTos[r], indexInfo: IndexInformation): ERelOp \ r = 
        let compileOpRec: ARelOp -> ERelOp \ r = x -> compileOp(x, rc, idToIndex, idToMarshall, marshall, writeTo, indexInfo);
        match op {
            case ASearch(rv, relSym, body) =>
                let compiledBody = compileOpRec(body);
                let thisWriteTo = getWriteTo(rv, writeTo);
                let placements = snd(indexInfo);
                let relPos = unwrap(Map.get((relSym, 0), placements));
                // let _ = rel;
                match toDenotation(relSym) {
                    case Denotation.Relational => (
                        ESearch(compileRowVar(rv, idToIndex), relPos, thisWriteTo, compiledBody)
                    )
                    case Denotation.Latticenal(bot, leq, lub, _) =>
                        ESearchLattice(compileRowVar(rv, idToIndex), relPos, ???, ???, thisWriteTo, compiledBody)

                }
                // if() {
                //     ESearch(compileRowVar(tpv), relPos, thisWriteTo, compiledBody)
                // } else {

                // }
            case AFunctional(rv, f, terms, body, arity) =>
                let RowVar.Named(id) = rv;
                let termToIndex = term -> unwrap(Map.get(getTermRamId(term), idToMarshall));
                let idToMarhsalled = id_ -> unwrap(Map.get(id_, idToMarshall));
                let from_ = Vector.map(termToIndex, terms);
                // let thisPosition = UniqueInts.getIndex(tpv, idToIndex);
                let compiledBody = compileOpRec(body);
                let thisWriteTo = getWriteTo(rv, writeTo);
                let to = Vector.map(i -> idToMarhsalled(RamId.TuplePos(id, i)), Vector.range(0, arity));
                EFunctional(
                    compileRowVar(rv, idToIndex), f, 
                    Vector.map(x -> compileTerm(x, idToIndex, idToMarshall, marshall), terms), 
                    thisWriteTo, compiledBody, from_, to
                )
            case AProject(terms, s) => 
                let (constructed, placements) = indexInfo;
                let newRelPos = unwrap(Map.get((s, 0), placements));
                let (bot, leq, lub) = match toDenotation(s) {
                    case Denotation.Relational => (
                        BoxedBool(false),
                        _ -> _ -> bug!("Using lattice logic on normal relation"),
                        _ -> _ -> bug!("Using lattice logic on normal relation")
                    )
                    case Denotation.Latticenal(bot, leq, lub, _) => (bot, leq, lub)
                };
                let compiledTerms = Vector.map(x -> compileTerm(x, idToIndex, idToMarshall, marshall), terms);
                EProject(
                    compiledTerms, newRelPos, bot, leq, lub, relSymToDenId(s, idToMarshall)
                )
            case AIf(boolExps, body) =>
                EIf(Vector.map(x -> compileBool(x, idToIndex, idToMarshall, marshall, indexInfo), boolExps), compileOpRec(body))
            case AQuery(rv, _, tests, index, body) =>
                // if(Vector.isEmpty(tests)) {
                    // let compiledTests = Vector.map(x -> compileBool(x, idToIndex, idToMarshall, marshall, indexInfo), tests);
                    // Remove the bools that are used for the index anyway.
                    let thisWriteTo = getWriteTo(rv, writeTo);
                    Vector.filterMap(x -> match x {
                        case ABoolExp.Eq(ARamTerm.RowLoad(rv1, i1, _), ARamTerm.RowLoad(rv2, i2, _)) if rv == rv1 =>
                            addWriteTo(rv2, i2, rv1, i1, idToIndex, writeTo);
                            None
                        case ABoolExp.Eq(ARamTerm.RowLoad(rv2, i2, _), ARamTerm.RowLoad(rv1, i1, _)) if rv == rv1 =>
                            addWriteTo(rv2, i2, rv1, i1, idToIndex, writeTo);
                            None
                        case _ => Some(x)
                    }, tests);
                    EQuery(compileRowVar(rv, idToIndex), index, thisWriteTo, compileOpRec(body))
                // } else {unchecked_cast(println(tests) as _ \ r); bug!("There should be no conditions at this point")}
            // case _ => ???
        }

    def compileTerm(term: ARamTerm, idToIndex: IdToIndex[r], idToMarshall: RamIdToMarshal, marshall: Boxing[r]): ERamTerm \ r =
        let compileT = x -> compileTerm(x, idToIndex, idToMarshall, marshall);
        // let termToIndex = term1 -> unwrap(Map.get(getTermRamId(term1), idToMarshall));
        let termToM = t -> unwrap(Map.get(getTermRamId(t), idToMarshall));
        let idToMarhsalled = id -> unwrap(Map.get(id, idToMarshall));
        match term {
            case ALit(val, id) => ELit(Boxing.debox(val, unwrap(Map.get(id, idToMarshall)), marshall), val)
            case ARowLoad(tpv, index, RelSym.Symbol(_, arity, den)) => 
                match den {
                    case Denotation.Relational => ELoadFromTuple(UniqueInts.getIndex(tpv, idToIndex), index, termToM(term))
                    case Denotation.Latticenal(_, _, _, _) => 
                        if(index < arity - 1) {
                            ELoadFromTuple(UniqueInts.getIndex(tpv, idToIndex), index, termToM(term))
                        } else {
                            ELoadLatVar(UniqueInts.getIndex(tpv, idToIndex))
                        }
                }
            case AMeet(f, t1, t2, _)                => EMeet(f, compileT(t1), compileT(t2), termToM(t1))
            case AApp0(f, id)                       => EApp0(f, idToMarhsalled(id))
            case AApp1(f, t1, id)                   => EApp1(f, compileT(t1), termToM(t1), idToMarhsalled(id))
            case AApp2(f, t1, t2, id)               => EApp2(f, compileT(t1), compileT(t2), termToM(t1), termToM(t2), idToMarhsalled(id))
            case AApp3(f, t1, t2, t3, id)           => EApp3(f, compileT(t1), compileT(t2), compileT(t3), termToM(t1), termToM(t2), termToM(t3), idToMarhsalled(id))
            case AApp4(f, t1, t2, t3, t4, id)       => EApp4(f, compileT(t1), compileT(t2), compileT(t3), compileT(t4), termToM(t1), termToM(t2), termToM(t3), termToM(t4), idToMarhsalled(id))
            case AApp5(f, t1, t2, t3, t4, t5, id)   => EApp5(f, compileT(t1), compileT(t2), compileT(t3), compileT(t4), compileT(t5), termToM(t1), termToM(t2), termToM(t3), termToM(t4), termToM(t5), idToMarhsalled(id))
    }

    def compileBool(bool: ABoolExp, map: IdToIndex[r], idToMarshall: RamIdToMarshal, marshall: Boxing[r], indexInfo: IndexInformation): EBoolExp \ r = 
        let termToIndex = term -> unwrap(Map.get(getTermRamId(term), idToMarshall));
        let compileT = x -> compileTerm(x, map, idToMarshall, marshall);
        match bool {
            case AIsEmpty(s) =>
                let (_, placements) = indexInfo;
                let sPos = unwrap(Map.get((s, 0), placements));
                EIsEmpty(sPos)
            case ANotMemberOf(terms, s) => 
                let (_, placements) = indexInfo;
                let leq = match toDenotation(s) {
                    case Denotation.Relational => _ -> _ -> bug!("Using lattice logic on normal relation")
                    case Denotation.Latticenal(_, leq, _, _) => leq
                };
                let sPos = unwrap(Map.get((s, 0), placements));
                ENotMemberOf(Vector.map(compileT, terms), sPos, leq, relSymToDenId(s, idToMarshall))
            case AEq(term1, term2) => 
                EEq(compileT(term1), compileT(term2))
            case AGuard0(f) => EGuard0(f)
            case AGuard1(f, term1) => EGuard1(f, compileT(term1), termToIndex(term1))
            case AGuard2(f, term1, term2) => EGuard2(f, compileT(term1), compileT(term2), termToIndex(term1), termToIndex(term2))
            case AGuard3(f, term1, term2, term3) => EGuard3(f, compileT(term1), compileT(term2), compileT(term3), termToIndex(term1), termToIndex(term2), termToIndex(term3))
            case AGuard4(f, term1, term2, term3, term4) => EGuard4(f, compileT(term1), compileT(term2), compileT(term3), compileT(term4), termToIndex(term1), termToIndex(term2), termToIndex(term3), termToIndex(term4))
            case AGuard5(f, term1, term2, term3, term4, term5) => EGuard5(f, compileT(term1), compileT(term2), compileT(term3), compileT(term4), compileT(term5), termToIndex(term1), termToIndex(term2), termToIndex(term3), termToIndex(term4), termToIndex(term5))
    }

    def compileRowVar(rowVar: RowVar, idToIndex: IdToIndex[r]): Int32 \ r = 
        UniqueInts.getIndex(rowVar, idToIndex)

    def getWriteTo(rowVar: RowVar, writeTo: WriteTos[r]): Vector[WriteTuple] \ r = 
        List.toVector(Option.getWithDefault(Nil, MutMap.get(rowVar, writeTo)))

    def addWriteTo(fromTuple: RowVar, fromIndex: Int32, toTuple: RowVar, toIndex: Int32, idToIndex: IdToIndex[r], writeTo: WriteTos[r]): Unit \ r =
        let written = (fromIndex, compileRowVar(toTuple, idToIndex), toIndex);
        MutMap.putWith(_ -> old -> written :: old, fromTuple, written :: Nil, writeTo)


    def unwrap(opt: Option[a]): a = match opt {
        case None => bug!("Unwrap None in Lowering")
        case Some(v) => v
    }


}