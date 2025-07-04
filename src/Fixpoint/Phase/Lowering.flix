/*
 * Copyright 2025 Casper Dalgaard Nielsen
 *                Adam Yasser Tallouzi
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

mod Fixpoint.Phase.Lowering {
    use Fixpoint.Ast.ExecutableRam.WriteTuple
    use Fixpoint.Ast.ExecutableRam.{BoolExp => EBoolExp, ConstWrites => EConstWrites, RamProgram => EProgram, RamStmt => ERamStmt, RamTerm => ERamTerm, RelOp => ERelOp}
    use Fixpoint.Ast.ExecutableRam.BoolExp.{Eq => EEq, Guard1 => EGuard1, Guard2 => EGuard2, Guard3 => EGuard3, Guard4 => EGuard4, Guard5 => EGuard5, IsEmpty => EIsEmpty, Leq => ELeq, Not => ENot, NotMemberOf => ENotMemberOf}
    use Fixpoint.Ast.ExecutableRam.RamTerm.{App1 => EApp1, App2 => EApp2, App3 => EApp3, App4 => EApp4, App5 => EApp5, LoadFromTuple => ELoadFromTuple, LoadLatVar => ELoadLatVar, Lit => ELit, Meet => EMeet, ProvMax => EProvMax}
    use Fixpoint.Ast.ExecutableRam.RelOp.{Functional => EFunctional, If => EIf, Project => EProject, Query => EQuery, Search => ESearch}
    use Fixpoint.Ast.Ram.{arityOf, arityOfNonLat, getTermRamId, IndexInformation, RamId, RelSym, RowVar, Search, toDenotation}
    use Fixpoint.Ast.Ram.{BoolExp => ABoolExp, RamProgram => AProgram, RamStmt => ARamStmt, RamTerm => ARamTerm, RelOp => ARelOp}
    use Fixpoint.Ast.Ram.BoolExp.{Eq => AEq, Guard1 => AGuard1, Guard2 => AGuard2, Guard3 => AGuard3, Guard4 => AGuard4, Guard5 => AGuard5, IsEmpty => AIsEmpty, Leq => ALeq, Not => ANot, NotMemberOf => ANotMemberOf, NotBot => ANotBot}
    use Fixpoint.Ast.Ram.RamTerm.{App1 => AApp1, App2 => AApp2, App3 => AApp3, App4 => AApp4, App5 => AApp5, Lit => ALit, Meet => AMeet, ProvMax => AProvMax, RowLoad => ARowLoad}
    use Fixpoint.Ast.Ram.RelOp.{Functional => AFunctional, If => AIf, Project => AProject, Query => AQuery, Search => ASearch}
    use Fixpoint.Ast.Shared.{Denotation, PredSym}
    use Fixpoint.Boxing
    use Fixpoint.BoxingType.{Boxing, RamIdToPos};
    use Fixpoint.UniqueInts
    use Fixpoint.Util.getOrCrash

    ///
    /// Maps RowVars to their memory-position (position in an array the interpreter will use).
    ///
    type alias IdToIndex[r: Region] = UniqueInts[RowVar, r]

    ///
    /// Maps RowVars to a lsit of writes that should be performed whenever the RowVar is rebound.
    ///
    type alias WriteTos[r: Region] = MutMap[RowVar, List[WriteTuple], r]

    ///
    /// Maps a memory position to writes. 
    ///
    /// As an example [2 => [0 => 38i64]] means that the first attribute of the RowVar placed
    /// at position 2 should have value 38.
    ///
    type alias ConstWrites[r: Region] = MutMap[Int32, MutMap[Int32, Int64, r], r]

    ///
    /// Contains information with relation to computing meets. For `(list, disjoint)` `list` will
    /// contain the currently bound `RowVar`'s in reverse order. `MutDisjointSets` contains
    /// information about which `RowVar`'s lattice-values are should be meeted.
    ///
    /// As an example consider
    /// ```
    /// search x ∈ A do
    ///   search y ∈ B do
    ///     project (0; Meet(x, y)) into ΔC'
    ///   end
    /// end
    /// ```
    /// 
    /// First MeetWithMap will be `(Nil, {})`. When it starts lowering `search y ∈ B do` it will
    /// have registered `x` and be `(x :: Nil, {})`. When it starts lowering `project` it will be
    /// `(y :: x :: Nil, {})`. It will then lower `Meet(x, y)` which updates `disjoint` so it now
    /// looks like `{y = x}`.
    ///
    /// The above code will be translated to something like
    /// ```
    /// search x ∈ A do
    ///   search y ∈ B do
    ///     project (0; Meet(x, y)) into ΔC'
    ///   end
    /// end
    /// ```
    type alias MeetWithMap[r: Region] = (List[RowVar], MutDisjointSets[RowVar, r])

    @Internal
    pub def lowerProgram(rc: Region[r], program: AProgram): (EProgram, Boxing[r]) \ r = match program { 
        case AProgram.Program(stmt, _, meta, indexInfo) =>
            let idToIndex = UniqueInts.empty(rc);
            let (marshall, newFacts, idToMarshall) = Boxing.initialize(rc, program);
            let writeTo = (MutMap.empty(rc), MutMap.empty(rc));
            let loweredStmt = lowerStmt(rc, idToIndex, (idToMarshall, marshall), writeTo, indexInfo, stmt);

            let constWrites = snd(writeTo) |> MutMap.foldWithKey(acc1 -> outerPos -> inner ->
                MutMap.foldLeftWithKey(acc2 -> innerPos -> value -> (outerPos, innerPos, value) :: acc2, acc1, inner)
            , Nil) |> List.toVector;
            // Compute arities
            let arityInformation = Fixpoint.Util.collectRowVarArity(program);
            let numOfArities = UniqueInts.get(idToIndex);
            let arities = Array.empty(rc, numOfArities);
            arityInformation |> List.forEach(match (rv, arity) -> Array.put(arity, UniqueInts.getIndex(rv, idToIndex), arities));
            (EProgram.Program(loweredStmt, newFacts, meta, indexInfo, (Array.toVector(arities), constWrites), idToMarshall), marshall)
    }

    def lowerStmt(rc: Region[r], idToIndex: IdToIndex[r], marshalling: (RamIdToPos, Boxing[r]), writeTo: (WriteTos[r], ConstWrites[r]), indexInfo: IndexInformation, stmt: ARamStmt): ERamStmt \ r =
        let lowerStmtRec = lowerStmt(rc, idToIndex, marshalling, writeTo, indexInfo);
        match stmt {
            case ARamStmt.Insert(op) =>
                let newOp = lowerOp(rc, idToIndex, marshalling, writeTo, indexInfo, (Nil, MutDisjointSets.empty(rc)), op);
                ERamStmt.Insert(newOp)

            // For all of these we have to do the operation for all indexes created for the relations.
            case ARamStmt.MergeInto(newRel, deltaRel) =>
                let (constructed, placements) = indexInfo;
                let newRelPos = getOrCrash(Map.get((newRel, 0), placements));
                let lowerToMerge = index -> ERamStmt.MergeInto(newRelPos, index, toDenotation(newRel));
                let deltaRels = Vector.length(getOrCrash(Map.get(deltaRel, constructed)));
                let merges = Vector.map(index -> lowerToMerge(getOrCrash(Map.get((deltaRel, index), placements))), Vector.range(0, deltaRels));
                if(Vector.length(merges) == 1) {
                    Vector.get(0, merges)
                } else {
                    ERamStmt.Par(merges)
                }
            case ARamStmt.Swap(newRel, deltaRel) =>
                let (constructed, placements) = indexInfo;
                let newRelPos = getOrCrash(Map.get((newRel, 0), placements));
                let lowerToMerge = index -> ERamStmt.MergeInto(newRelPos, index, toDenotation(newRel));
                let lowerToPurge = index -> ERamStmt.Purge(index);
                let deltaRels = Vector.length(getOrCrash(Map.get(deltaRel, constructed)));
                let swapPart = ERamStmt.Swap(newRelPos, getOrCrash(Map.get((deltaRel, 0), placements)));
                if (deltaRels == 1) {
                    swapPart
                } else {
                    let merges = 
                        Vector.range(1, deltaRels) |>
                        Vector.map(index -> lowerToMerge(getOrCrash(Map.get((deltaRel, index), placements))));
                    let purges = Vector.range(1, deltaRels) |>
                        Vector.map(index -> lowerToPurge(getOrCrash(Map.get((deltaRel, index), placements))));
                    if(Vector.length(merges) == 1) {
                        ERamStmt.Seq(Vector#{Vector.get(0, merges), swapPart})
                    } else {
                        ERamStmt.Seq(Vector#{ERamStmt.Seq(purges), ERamStmt.Par(merges), swapPart})
                    }
                }
            case ARamStmt.Purge(s) =>
                let (constructed, placements) = indexInfo;
                let indexNums = Vector.range(0, Vector.length(getOrCrash(Map.get(s, constructed))));
                let purges = Vector.map(i -> ERamStmt.Purge(getOrCrash(Map.get((s, i), placements))), indexNums);
                if (Vector.length(purges) == 1) {
                    Vector.get(0, purges)
                } else {
                    ERamStmt.Seq(purges)
                }
            case ARamStmt.Seq(xs) => Vector.map(x -> lowerStmtRec(x), xs) |> ERamStmt.Seq
            case ARamStmt.Par(xs) => Vector.map(x -> lowerStmtRec(x), xs) |> ERamStmt.Par
            case ARamStmt.Until(test, body) => ERamStmt.Until(Vector.filterMap(lowerBool(idToIndex, marshalling, indexInfo, (Nil, MutDisjointSets.empty(rc))), test), lowerStmtRec(body))
            case ARamStmt.EstimateJoinSize(_, relIndex, estWriteTo, attr) => 
                ERamStmt.EstimateJoinSize(relIndex, estWriteTo, attr)
            case ARamStmt.Comment(s) => ERamStmt.Comment(s)
    }

    def addRowVarToMeetWithMap(rv: RowVar, meetWithMap: MeetWithMap[r]): MeetWithMap[r] \ r =
        let (prevRowVars, meetDisjointSet) = meetWithMap;
        MutDisjointSets.makeSet(rv, meetDisjointSet);
        (rv :: prevRowVars, meetDisjointSet)

    def computeMeetWithPos(
        rv: RowVar,
        relSym: RelSym,
        idToIndex: IdToIndex[r],
        meetWithMap: MeetWithMap[r]
    ): Int32 \ r = match toDenotation(relSym) {
        case Denotation.Relational => -1
        case Denotation.Latticenal(_, _, _, _) => computeLatticeMeetPos(rv, idToIndex, meetWithMap)
    }
    
    def computeLatticeMeetPos(
        rv: RowVar,
        idToIndex: IdToIndex[r],
        meetWithMap: MeetWithMap[r]
    ): Int32 \ r = {
        let (prevRowVars, meetDisjointSet) = meetWithMap;
        let firstMatching = List.findLeft(x -> MutDisjointSets.equivalent(rv, x, meetDisjointSet), prevRowVars);
        match firstMatching {
            case None => lowerRowVar(rv, idToIndex)
            case Some(v) => lowerRowVar(v, idToIndex)
        }
    }

    def lowerOp(
        rc: Region[r],
        idToIndex: IdToIndex[r],
        marshalling: (RamIdToPos, Boxing[r]), 
        writeTo: (WriteTos[r], ConstWrites[r]), 
        indexInfo: IndexInformation,
        meetWithMap: MeetWithMap[r],
        op: ARelOp
    ): ERelOp \ r =
        let lowerOpRec = lowerOp(rc, idToIndex, marshalling, writeTo, indexInfo, meetWithMap);
        let lowerOpRecNewRowVar = rv -> lowerOp(rc, idToIndex, marshalling, writeTo, indexInfo, addRowVarToMeetWithMap(rv, meetWithMap));
        match op {
            case ASearch(rv, relSym, body) =>
                let den = toDenotation(relSym);
                let loweredBody = lowerOpRecNewRowVar(rv, body);
                let thisWriteTo = getWriteTo(rv, writeTo);
                let placements = snd(indexInfo);
                let relPos = getOrCrash(Map.get((relSym, 0), placements));
                let oldPos = computeMeetWithPos(rv, relSym, idToIndex, meetWithMap);
                ESearch(lowerRowVar(rv, idToIndex), relPos, oldPos, den, thisWriteTo, loweredBody)
            case AQuery(rv, relSym, tests, index, body) =>
                let den = toDenotation(relSym);
                let (idToMarshall, marshall) = marshalling;
                let loweredBody = lowerOpRecNewRowVar(rv, body);
                let oldPos = computeMeetWithPos(rv, relSym, idToIndex, meetWithMap);
                let thisWriteTo = getWriteTo(rv, writeTo);
                let otherBools = Vector.filterMap(x -> match x {
                    case ABoolExp.Eq(ARamTerm.RowLoad(rv1, i1, _), ARamTerm.RowLoad(rv2, i2, _)) if rv == rv1 =>
                        addWriteTo(rv2, i2, rv1, i1, idToIndex, writeTo);
                        None
                    case ABoolExp.Eq(ARamTerm.RowLoad(rv2, i2, _), ARamTerm.RowLoad(rv1, i1, _)) if rv == rv1 =>
                        addWriteTo(rv2, i2, rv1, i1, idToIndex, writeTo);
                        None
                    case ABoolExp.Eq(ARamTerm.RowLoad(rv1, i, _), ARamTerm.Lit(val, id)) if rv == rv1 =>
                        let unboxed = Boxing.unboxWith(val, getOrCrash(Map.get(id, idToMarshall)), marshall);
                        addConstWriteTo(unboxed, rv, i, idToIndex, writeTo, rc);
                        None
                    case ABoolExp.Eq(ARamTerm.Lit(val, id), ARamTerm.RowLoad(rv1, i, _)) if rv == rv1 =>
                        let unboxed = Boxing.unboxWith(val, getOrCrash(Map.get(id, idToMarshall)), marshall);
                        addConstWriteTo(unboxed, rv, i, idToIndex, writeTo, rc);
                        None
                    case _ => Some(x)
                }, tests);
                if(Vector.length(otherBools) != 0)
                    unchecked_cast(bug!("Bug in Fixpoint.Lowering: Bools except equality in query") as _ \ r) 
                else ();
                EQuery(lowerRowVar(rv, idToIndex), index, oldPos, den, thisWriteTo, loweredBody)
            case AFunctional(rv, f, terms, body, arity) =>
                let (idToMarshall, _) = marshalling;
                let idToMarhsalled = id -> getOrCrash(Map.get(id, idToMarshall));
                let loweredBody = lowerOpRec(body);
                let thisWriteTo = getWriteTo(rv, writeTo);
                let to = Vector.map(i -> idToMarhsalled(RamId.TuplePos(rv, i)), Vector.range(0, arity));
                EFunctional(
                    lowerRowVar(rv, idToIndex), f, 
                    Vector.map(lowerTerm(idToIndex, marshalling, meetWithMap), terms), 
                    thisWriteTo, loweredBody, to
                )
            case AProject(terms, s, _) => 
                let (_, placements) = indexInfo;
                let newRelPos = getOrCrash(Map.get((s, 0), placements));
                let den = toDenotation(s);
                let loweredTerms = Vector.map(lowerTerm(idToIndex, marshalling, meetWithMap), terms);
                EProject(
                    loweredTerms, newRelPos, den
                )
            case AIf(boolExps, body) =>
                EIf(Vector.filterMap(lowerBool(idToIndex, marshalling, indexInfo, meetWithMap), boolExps), lowerOpRec(body))
        }

    def lowerTerm(
        idToIndex: IdToIndex[r], 
        marshalling: (RamIdToPos, Boxing[r]), 
        meetWithMap: MeetWithMap[r],
        term: ARamTerm
    ): ERamTerm \ r =
        let lowerT = lowerTerm(idToIndex, marshalling, meetWithMap);
        let (idToMarshall, marshall) = marshalling;
        let termToM = t -> getOrCrash(Map.get(getTermRamId(t), idToMarshall));
        match term {
            case ALit(val, id) => ELit(Boxing.unboxWith(val, getOrCrash(Map.get(id, idToMarshall)), marshall), val)
            case AProvMax(vec) =>
                vec |>
                Vector.map(match (rv, i) -> (UniqueInts.getIndex(rv, idToIndex), i)) |>
                EProvMax
            case ARowLoad(rv, index, RelSym.Symbol(_, arity, den)) => 
                match den {
                    case Denotation.Relational => ELoadFromTuple(UniqueInts.getIndex(rv, idToIndex), index, termToM(term))
                    case Denotation.Latticenal(_, _, _, _) => 
                        if(index < arity - 1) {
                            ELoadFromTuple(UniqueInts.getIndex(rv, idToIndex), index, termToM(term))
                        } else {
                            ELoadLatVar(UniqueInts.getIndex(rv, idToIndex), termToM(term))
                        }
                }
            case AMeet(_, _, _, _) =>
                let representingRowVar = lowerMeet(term, idToIndex, meetWithMap);
                let pos = computeLatticeMeetPos(representingRowVar, idToIndex, meetWithMap);
                ELoadLatVar(pos, termToM(term))
            case AApp1(f, t1, _)                   => EApp1(f, lowerT(t1), termToM(term))
            case AApp2(f, t1, t2, _)               => EApp2(f, lowerT(t1), lowerT(t2), termToM(term))
            case AApp3(f, t1, t2, t3, _)           => EApp3(f, lowerT(t1), lowerT(t2), lowerT(t3), termToM(term))
            case AApp4(f, t1, t2, t3, t4, _)       => EApp4(f, lowerT(t1), lowerT(t2), lowerT(t3), lowerT(t4), termToM(term))
            case AApp5(f, t1, t2, t3, t4, t5, _)   => EApp5(f, lowerT(t1), lowerT(t2), lowerT(t3), lowerT(t4), lowerT(t5), termToM(term))
        }

    def lowerMeet(
        term: ARamTerm,
        idToIndex: IdToIndex[r],
        meetWithMap: MeetWithMap[r]
    ): RowVar \ r = match term {
        case ARowLoad(rv, _, _) =>
            let (_, meetDisjointSet) = meetWithMap;
            MutDisjointSets.makeSet(rv, meetDisjointSet);
            rv
        case AMeet(_, t1, (rv, _), _) => 
            let (_, meetDisjointSet) = meetWithMap;
            let prevRv = lowerMeet(t1, idToIndex, meetWithMap);
            MutDisjointSets.makeSet(rv, meetDisjointSet);
            MutDisjointSets.makeSet(prevRv, meetDisjointSet);
            MutDisjointSets.union(rv, prevRv, meetDisjointSet);
            rv
        case _ => unreachable!()
    }
    
    // NotBot is removed as it is handled separately by the interpreter.
    def lowerBool(
        idToIndex: IdToIndex[r],
        marshalling: (RamIdToPos, Boxing[r]),
        indexInfo: IndexInformation,
        meetWithMap: MeetWithMap[r],
        bool: ABoolExp
    ): Option[EBoolExp] \ r = 
        let lowerT = lowerTerm(idToIndex, marshalling, meetWithMap);
        match bool {
            case ANot(s) => 
                lowerBool(idToIndex, marshalling, indexInfo, meetWithMap, s) |>
                Option.map(ENot)
            case AIsEmpty(s) =>
                let (_, placements) = indexInfo;
                let sPos = getOrCrash(Map.get((s, 0), placements));
                Some(EIsEmpty(sPos))
            case ANotMemberOf(terms, s) => 
                let (_, placements) = indexInfo;
                let den = toDenotation(s);
                let sPos = getOrCrash(Map.get((s, 0), placements));
                Some(ENotMemberOf(Vector.map(lowerT, terms), sPos, den))
            case ANotBot(t1, _, _) => 
                lowerMeet(t1, idToIndex, meetWithMap);
                None
            case ALeq(box, rv, relSym) =>
                let leq = match toDenotation(relSym) {
                    case Denotation.Relational => _ -> _ -> bug!("Using lattice logic on normal relation")
                    case Denotation.Latticenal(_, leq, _, _) => leq
                };
                Some(ELeq(box, leq, lowerRowVar(rv, idToIndex)))
            case AEq(term1, term2) => 
                Some(EEq(lowerT(term1), lowerT(term2)))
            case AGuard1(f, term1) => Some(EGuard1(f, lowerT(term1)))
            case AGuard2(f, term1, term2) => Some(EGuard2(f, lowerT(term1), lowerT(term2)))
            case AGuard3(f, term1, term2, term3) => Some(EGuard3(f, lowerT(term1), lowerT(term2), lowerT(term3)))
            case AGuard4(f, term1, term2, term3, term4) => Some(EGuard4(f, lowerT(term1), lowerT(term2), lowerT(term3), lowerT(term4)))
            case AGuard5(f, term1, term2, term3, term4, term5) => Some(EGuard5(f, lowerT(term1), lowerT(term2), lowerT(term3), lowerT(term4), lowerT(term5)))
        }

    def lowerRowVar(rowVar: RowVar, idToIndex: IdToIndex[r]): Int32 \ r = 
        UniqueInts.getIndex(rowVar, idToIndex)

    def getWriteTo(rowVar: RowVar, writeTo: (WriteTos[r], ConstWrites[r])): Vector[WriteTuple] \ r = 
        let varWrite = fst(writeTo);
        List.toVector(Option.getWithDefault(Nil, MutMap.get(rowVar, varWrite)))

    def addWriteTo(fromTuple: RowVar, fromIndex: Int32, toTuple: RowVar, toIndex: Int32, idToIndex: IdToIndex[r], writeTo: (WriteTos[r], ConstWrites[r])): Unit \ r =
        let varWrite = fst(writeTo);
        let written = (fromIndex, lowerRowVar(toTuple, idToIndex), toIndex);
        MutMap.putWith(_ -> old -> written :: old, fromTuple, written :: Nil, varWrite)

    def addConstWriteTo(value: Int64, toTuple: RowVar, toIndex: Int32, idToIndex: IdToIndex[r], writeTo: (WriteTos[r], ConstWrites[r]), rc: Region[r]): Unit \ r =
        let constWrite = snd(writeTo);
        let toTuplePos = lowerRowVar(toTuple, idToIndex);
        MutMap.getOrElsePut(toTuplePos, MutMap.empty(rc), constWrite) |>
            MutMap.putWith(v1 -> v2 -> 
                if (v1 != v2) 
                    bug!("Bug in Fixpoint.Lowering: Different value for position. Should have been removed by Hoisting")
                else v1
            , toIndex, value)

}