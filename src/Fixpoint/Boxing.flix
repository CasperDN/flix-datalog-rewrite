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

///
/// The purpose of this file is to map boxed constants to Int64 
/// since the indices on relations work on Int64 due to the lower
/// complexity of working with integers.
///
mod Fixpoint.Boxing {
    use Fixpoint.Boxed
    use Fixpoint.Boxable
    use Fixpoint.Ast.Ram
    use Fixpoint.Ast.Ram.{RamId, RamStmt, RelOp, RamTerm, BoolExp, RelSym, RamProgram, arityOf, arityOfNonLat, toDenotation}
    use Fixpoint.Ast.ExecutableRam.{Facts => EFacts}
    use Fixpoint.Ast.Datalog.{Datalog}
    use Fixpoint.Boxed.{BoxedBool, BoxedChar, BoxedInt8, BoxedInt16, BoxedInt32, BoxedInt64, BoxedFloat32, BoxedFloat64, BoxedObject}
    use Fixpoint.Ast.Shared.{PredSym, isRelational, Denotation}
    use Fixpoint.Predicates.relSymsOfProgram
    use Fixpoint.BoxingTypes.{Boxing, TypeInfo, Lock, Types, setType, getType, RamIdToPos, AtomicCounter, UnifiedTypePos}
    import java.lang.{Float, Double, Object, Character, Runtime}

    // @Internal
    // pub def initialize(rc: Region[r], program: RamProgram): (Boxing[r], RamIdToPos) \ r =
    //     let mapping = Equality.computeMapping(program);
    //     let boxingInfo = initializeInternal(rc, program, mapping);
    //     // let facts = initializeFacts(rc, program, boxingInfo, mapping);
    //     (boxingInfo, mapping)

    @Internal
    pub def initialize(rc: Region[r], program: RamProgram): (Boxing[r], EFacts, RamIdToPos) \ r =
        let mapping = Equality.computeMapping(program);
        let boxingInfo = initializeInternal(rc, program, mapping);
        let (facts, newBoxingInfo) = initializeFacts(rc, program, boxingInfo, mapping);
        (newBoxingInfo, facts, mapping)

    def initializeFacts(rc1: Region[r], program: RamProgram, boxingInfo: Boxing[r], mapping: RamIdToPos): (EFacts, Boxing[r]) \ r = region rc2 {        
        let RamProgram.Program(_, facts, _, _) = program;
        let factsAsVec = Map.toVector(facts);
        let counters = initializeCounters(rc1, boxingInfo);
        let newFacts = Array.empty(rc2, Vector.length(factsAsVec));
        let funcsToBeRun = factsAsVec |> Vector.mapWithIndex(i -> match (relSym, factVec) -> () -> {
            let mappedResult = mapAllFacts(rc1, relSym, factVec, boxingInfo, counters, mapping);
            Array.put((relSym, mappedResult), i, newFacts)
        });
        spawnFuncs(funcsToBeRun);
        let newBoxing = fixBoxingAfterInit(rc1, counters, boxingInfo);
        (Array.toMap(newFacts), newBoxing)
    }

    def fixBoxingAfterInit(rc: Region[r], counters: Vector[AtomicCounter[r]], boxingInfo: Boxing[r]): Boxing[r] \ r = {
        let (_, boxToRepVec, typeInfo, locks) = boxingInfo;
        let newBoxedArr = counters |> Vector.map(c -> Array.empty(rc, unwrap(Int64.tryToInt32(AtomicCounter.peek(c)))));
        let funcsToBeRun = newBoxedArr |>
            Vector.mapWithIndex(i -> writeTo -> () -> {
                match getType(i, typeInfo) {
                    case Types.Object =>
                        let boxToRep = Vector.get(i, boxToRepVec);
                        boxToRep |> BPlusTree.forEach(val -> pos -> Array.put(val, unwrap(Int64.tryToInt32(pos)), writeTo))
                    case _ => ()
                }
            });
        spawnFuncs(funcsToBeRun);
        let newMutLists = newBoxedArr |> Vector.map(Array.toMutList(rc));
        (newMutLists, boxToRepVec, typeInfo, locks)
    }

    def spawnFuncs(funcs: Vector[Unit -> Unit \ ef]): Unit \ ef = region rc2 {
        unchecked_cast({
            let _: Unit = spawn unchecked_cast(
                funcs |> Vector.forEach(f -> f())
            as _ \ IO) @ rc2;
            ()
        } as _ \ ef)
    }

    ///
    /// Returns the number of threads to use for parallel evaluation.
    ///
    /// # SAFETY:
    /// This accesses the runtime environment, which is an effect.
    /// It is assumed that this function is only used in contexts
    /// where this effect is not observable outside of the RedBlackTree module.
    ///
    /// Copy pasted from RedBlackTree.flix.
    ///
    def threads(): Int32 = unsafe {
        // Note: We use a multiple of the number of physical cores for better performance.
        let multiplier = 4;
        multiplier * Runtime.getRuntime().availableProcessors()
    }

            // let newFacts =
            //     facts |>
            //     Map.mapWithKey(k -> values ->
            //         let RelSym.Symbol(PredSym.PredSym(_, id), _, den) = k;
            //         values |> 
            //         Vector.map(vec -> match den {
            //             case Denotation.Relational =>
            //                 let tuple = vec |>
            //                     Vector.mapWithIndex(i -> v -> {
            //                         Boxing.unboxWith(v, unwrap(Map.get(RamId.RelPos(id, i), idToMarshall)), marshall)
            //                     });
            //                 (tuple, Boxed.None)
            //             case Denotation.Latticenal(_, _, _ ,_) =>
            //                 let len = Vector.length(vec);
            //                 let tuple = Array.empty(rc, len - 1);
            //                 vec |> Vector.forEachWithIndex(i -> term -> {
            //                     if (i < len - 1)
            //                         Array.put(Boxing.unboxWith(term, unwrap(Map.get(RamId.RelPos(id, i), idToMarshall)), marshall), i, tuple)
            //                     else ()
            //                 });
            //                 let latVal = Vector.get(len - 1, vec);
            //                 (Array.toVector(tuple), latVal)
            //         })
            //     );

    def mapAllFacts(rc1: Region[r],
        relSym: RelSym,
        facts: Vector[Vector[Boxed]],
        boxingInfo: Boxing[r],
        counters: Vector[AtomicCounter[r]],
        mapping: RamIdToPos
    ): Vector[(Vector[Int64], Boxed)] \ r = {
        let relSymId = Ram.toId(relSym);
        let positions = Vector.range(0, arityOf(relSym)) |>
            Vector.map(i -> unwrap(Map.get(RamId.RelPos(relSymId, i), mapping)));
        let threadNum = threads();
        let numOfFacts = Vector.length(facts);
        let resultArr = Array.empty(rc1, numOfFacts);
        if(numOfFacts <= threadNum) {
            mapPartOfVector(facts, 0, numOfFacts, isRelational(toDenotation(relSym)), resultArr, boxingInfo, counters, positions)
        } else {
            let inc = numOfFacts / threadNum;
            let limits = Array.init(rc1, i -> (i * inc, (i + 1) * inc), threadNum);
            Array.put((fst(Array.get(threadNum - 1, limits)), numOfFacts), threadNum, limits);
            let funcsToBeRun = limits |>
            Array.toVector |>
            Vector.map(match (lower, upper) ->
                () -> mapPartOfVector(facts, lower, upper, isRelational(toDenotation(relSym)), resultArr, boxingInfo, counters, positions)
            );
            spawnFuncs(funcsToBeRun)
        };
        Array.toVector(resultArr)
    }

    def mapPartOfVector(
        factVec: Vector[Vector[Boxed]],
        from_: Int32,
        to_: Int32,
        isRelational: Bool,
        collectionArr: Array[(Vector[Int64], Boxed), r],
        boxingInfo: Boxing[r],
        counters: Vector[AtomicCounter[r]],
        unifiedPositions: Vector[UnifiedTypePos]
    ): Unit \ r = {
        def loop(i) =
            if(i >= to_) ()
            else {
                let fullTuple = Vector.get(i, factVec);
                let (tuple, boxed) = if(isRelational) {
                    (fullTuple, Boxed.None)
                } else {
                    (Vector.dropRight(1, fullTuple), Vector.get(Vector.length(fullTuple) - 1, fullTuple))
                };
                let savedVec = tuple |>
                    Vector.mapWithIndex(index -> boxedVal ->
                        let unifiedPos = Vector.get(index, unifiedPositions);
                        match boxedVal {
                            case BoxedObject(_, _) =>
                                let (_, boxToRepVec, symInfo, _) = boxingInfo;
                                setType(Types.Object, unifiedPos, symInfo);
                                let boxToRep = Vector.get(unifiedPos, boxToRepVec);
                                let counter = Vector.get(unifiedPos, counters);
                                let rep = BPlusTree.computeIfAbsent(() -> AtomicCounter.getAndIncrement(counter), boxedVal, boxToRep);
                                rep
                            case _ => unboxWith(boxedVal, unifiedPos, boxingInfo)
                        }
                    );
                Array.put((savedVec, boxed), from_ + i, collectionArr);
                loop(i + 1)
            };
        loop(from_)
    }

    def initializeCounters(rc: Region[r], boxingInfo: Boxing[r]): Vector[AtomicCounter[r]] \ r = {
        let (boxedVecList, _, _, _) = boxingInfo;
        boxedVecList |>
            Vector.map(listOfBoxed ->  AtomicCounter.mkCounter(rc, Int32.toInt64(MutList.length(listOfBoxed))))
    }

    // def getMaxUnifiedTypePos(boxingInfo: Boxing[r]): UnifiedTypePos = {
    //     let (_, _, _, locks) = boxingInfo;
    //     Vector.length(locks) - 1
    // }

    def initializeInternal(rc: Region[r], program: RamProgram, map: RamIdToPos): Boxing[r] \ r =
        let max = 1 + snd(Option.getWithDefault((RamId.Id(-1), -1), Map.maximumValue(map)));
        let intToBox = Vector.init(_ -> MutList.empty(rc), max);
        let boxToInt = Vector.init(_ -> BPlusTree.empty(rc), max);
        let locks = Vector.init(_ -> Lock.mkLock(rc), max);
        let posToIndex = Array.empty(rc, max);
        let info = (intToBox, boxToInt, TypeInfo.TypeInfo(posToIndex), locks);
        let relSyms = relSymsOfProgram(program);
        // Add bot first to make sure it corresponds to 0.
        List.filter(match RelSym.Symbol(_, _, den) -> not isRelational(den), relSyms) |>
            List.forEach(x -> match x {
                case RelSym.Symbol(PredSym.PredSym(_, index), arity, Denotation.Latticenal(bot, _, _, _)) =>
                    unboxWith(bot, unwrap(Map.get(RamId.RelPos(index, arity - 1), map)), info); ()
                case _ => bug!("Should have been filtered out")
        });
        info

    def deMarshalObject(value: Int64, index: Int32, info: Boxing[r]): Boxed \ r = {
        let (objectList, _, _, locks) = info;
        let lock = Vector.get(index, locks);
        Lock.readLock(lock);
        let res = unwrap(MutList.nth(unwrap(Int64.tryToInt32(value)), Vector.get(index, objectList)));
        Lock.unlockRead(lock);
        res
    }

    def marshallObject(box: Boxed, index: Int32, info: Boxing[r]): Int64 \ r = {
        let (objectLists, vecObjectMap, _, locks) = info;
        let objectList = Vector.get(index, objectLists);
        let objectMap = Vector.get(index, vecObjectMap);
        let lock = Vector.get(index, locks);
        Lock.readLock(lock);
        match BPlusTree.get(box, objectMap) {
            case Some(id) => 
                Lock.unlockRead(lock);
                id
            case None =>
                Lock.unlockRead(lock);
                Lock.writeLock(lock);
                let id = getNextIndex(objectList);
                MutList.insert(box, id, objectList);
                BPlusTree.put(box, Int32.toInt64(id), objectMap);
                Lock.unlockWrite(lock);
                Int32.toInt64(id)
        }
    }

    def getNextIndex(list: MutList[Boxed, r]): Int32 \ r = {
        MutList.size(list)
    }

    pub def unboxWith(box: Boxed, index: Int32, info: Boxing[r]): Int64 \ r =
        let (_, _, symInfo, _) = info;
        match box {
            case BoxedBool(x)       => setType(Types.Bool, index, symInfo); if (x) 1i64 else 0i64
            case BoxedChar(x)       => setType(Types.Char, index, symInfo); Int32.toInt64(Char.toBmpCodePoint(x))
            case BoxedInt8(x)       => setType(Types.Int8, index, symInfo); Int8.toInt64(x)
            case BoxedInt16(x)      => setType(Types.Int16, index, symInfo); Int16.toInt64(x)
            case BoxedInt32(x)      => setType(Types.Int32, index, symInfo); Int32.toInt64(x)
            case BoxedInt64(x)      => setType(Types.Int64, index, symInfo); x
            case BoxedFloat32(x)    => setType(Types.Float32, index, symInfo); Int32.toInt64(Float.floatToRawIntBits(Float32.valueOf(x).floatValue()))
            case BoxedFloat64(x)    => setType(Types.Float64, index, symInfo); Double.doubleToRawLongBits(Float64.valueOf(x).doubleValue())
            case BoxedObject(_, _)  => setType(Types.Object, index, symInfo); marshallObject(box, index, info) // We remap to low, so only goes wrong when dealing with more than 2^32 different RelSyms
            case Boxed.None         => bug!("None should never be in a position to be unboxed unboxed")
        }

    pub def boxWith(v: Int64, index: Int32, info: Boxing[r]): Boxed \ r = 
        let (_, _, symInfo, _) = info;
        match getType(index, symInfo) {
            case Types.Bool      => Boxed.BoxedBool(not(v == 0i64))
            case Types.Char      => BoxedChar(unchecked_cast(Array.get(0, Character.toChars(unwrap(Int64.tryToInt32(v)))) as _ \ {}))
            case Types.Int8      => BoxedInt8(unwrap(Int64.tryToInt8(v)))
            case Types.Int16     => BoxedInt16(unwrap(Int64.tryToInt16(v)))
            case Types.Int32     => BoxedInt32(unwrap(Int64.tryToInt32(v)))
            case Types.Int64     => BoxedInt64(v)
            case Types.Float32   => BoxedFloat32(Float.intBitsToFloat(unwrap(Int64.tryToInt32(v))))
            case Types.Float64   => BoxedFloat64(Double.longBitsToDouble(v))
            case Types.Object    => deMarshalObject(v, index, info)
            case Types.Unknown   => bug!("Unormalizing value, which has never been normalized")
        }


    // Compute equality for the terms, deciding what can safely be stored together. Might miss some, but only a problem for objects.
    // Equality is on the full symbols.
    mod Equality {
        use Fixpoint.Ast.Ram.getTermRamId
        use Fixpoint.Ast.Ram
        use Fixpoint.Ast.Ram.{RamId, Predicates, RamStmt, RelOp, RamTerm, BoolExp, RamProgram, RowVar}
        use Fixpoint.Predicates.{PredType, idToFullPredID, fullIDtoPredType, relSymsOfProgram}
        use Fixpoint.Ast.Ram.{RelSym, RamProgram}
        use Fixpoint.BoxingTypes.RamIdToPos
        use Fixpoint.Ast.Shared.PredSym
        use Fixpoint.Counter
        use Fixpoint.Counter.Counter

        pub def computeMapping(d: RamProgram): RamIdToPos = region rc {
            let disjointSet = MutDisjointSets.empty(rc);
            let RamProgram.Program(s, _, predTrack, _) = d;
            computeDisjoint(d, disjointSet);
            let relSyms = relSymsOfProgram(d);
            let mutMap = MutMap.empty(rc);
            let counter = Counter.fresh(rc);
            List.forEach(match RelSym.Symbol(PredSym.PredSym(_, id), arity, _) -> {
                Vector.forEach(i -> {
                    insertIndex(RamId.RelPos(id, i), disjointSet, mutMap, counter)
                }, Vector.range(0, arity))
            }, relSyms);
            computeMappingStmt(s, predTrack, disjointSet, mutMap, counter);
            MutMap.toMap(mutMap)
        }

        def computeDisjoint(d: RamProgram, set: MutDisjointSets[RamId, r]): Unit \ r = match d {
            case RamProgram.Program(stmt, _, predTrack, _) =>
                let relSyms = relSymsOfProgram(d);
                List.forEach(match RelSym.Symbol(PredSym.PredSym(_, id), arity, _) -> {
                    unifyPredTypes(id, arity, predTrack, set)
                }, relSyms);
                computeDisjointStmt(stmt, predTrack, set)
        }

        def computeDisjointStmt(s: RamStmt, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RamStmt.Insert(rest) => computeDisjointOp(rest, predTrack, set)
            case RamStmt.MergeInto(rel1, rel2) => unifyPredicates(rel1, rel2, set)
            case RamStmt.Swap(rel1, rel2) => unifyPredicates(rel1, rel2, set)
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(x -> computeDisjointStmt(x, predTrack, set), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(x -> computeDisjointStmt(x, predTrack, set), stmts)
            case RamStmt.Until(bools, stmt) => computeDisjointStmt(stmt, predTrack, set); Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools)
            case RamStmt.Comment(_) => ()
            case RamStmt.EstimateJoinSize(_, _, _, _) => ()
        }

        def computeDisjointOp(s: RelOp, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RelOp.Search(rv, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), rest) =>
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.TuplePos(rv, i), set), Vector.range(0, arity));
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                Vector.forEach(i -> MutDisjointSets.union(RamId.TuplePos(rv, i), RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                unifyPredTypes(predSym, arity, predTrack, set);
                computeDisjointOp(rest, predTrack, set)
            case RelOp.Query(rv, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), bools, _, rest) =>
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.TuplePos(rv, i), set), Vector.range(0, arity));
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                Vector.forEach(i -> MutDisjointSets.union(RamId.TuplePos(rv, i), RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                unifyPredTypes(predSym, arity, predTrack, set);
                Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools);
                computeDisjointOp(rest, predTrack, set)
            case RelOp.Functional(RowVar.Named(id), _, inputTerms, rest, arity) =>
                Vector.forEachWithIndex(i -> curTerm -> {
                    let termID = Ram.getTermRamId(curTerm);
                    MutDisjointSets.makeSet(RamId.InId(id, i), set);
                    MutDisjointSets.makeSet(termID, set);
                    MutDisjointSets.union(RamId.InId(id, i), termID, set);
                    computeDisjointTerm(curTerm, predTrack, set)
                }, inputTerms);
                Vector.range(0, arity) |>
                Vector.forEach(i -> 
                    MutDisjointSets.makeSet(RamId.TuplePos(RowVar.Named(id), i), set)
                );
                computeDisjointOp(rest, predTrack, set)
            case RelOp.Project(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                unifyPredTypes(predSym, arity, predTrack, set);
                Vector.forEachWithIndex(i -> term ->{
                    computeDisjointTerm(term, predTrack, set);
                    let termID = Ram.getTermRamId(term);
                    MutDisjointSets.makeSet(RamId.RelPos(predSym, i), set);
                    MutDisjointSets.makeSet(termID, set);
                    MutDisjointSets.union(RamId.RelPos(predSym, i), termID, set)
                }, terms);
                ()
            case RelOp.If(bools, rest) =>
                Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools);
                computeDisjointOp(rest, predTrack, set)
        }

        def computeDisjointBool(s: BoolExp, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case BoolExp.Not(boolExp) => computeDisjointBool(boolExp, predTrack, set)
            case BoolExp.IsEmpty(_) => ()
            case BoolExp.NotMemberOf(terms, RelSym.Symbol(PredSym.PredSym(_, id), _, _)) =>
                Vector.forEach(term -> computeDisjointTerm(term, predTrack, set), terms);
                Vector.forEachWithIndex(i -> term -> {
                    MutDisjointSets.makeSet(Ram.getTermRamId(term), set);
                    MutDisjointSets.makeSet(RamId.RelPos(id, i), set);
                    MutDisjointSets.union(Ram.getTermRamId(term), RamId.RelPos(id, i), set)
                }, terms)
            case BoolExp.NotBot(term, _, _) => computeDisjointTerm(term, predTrack, set)
            case BoolExp.Leq(_, _, _) => ()
            case BoolExp.Eq(term1, term2) =>
                computeDisjointTerm(term1, predTrack, set);
                computeDisjointTerm(term2, predTrack, set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.union(Ram.getTermRamId(term1), Ram.getTermRamId(term2), set)
            case BoolExp.Guard1(_, term1) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                computeDisjointTerm(term1, predTrack, set)
            case BoolExp.Guard2(_, term1, term2) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                computeDisjointTerm(term1, predTrack, set);
                computeDisjointTerm(term2, predTrack, set)
            case BoolExp.Guard3(_, term1, term2, term3) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term3), set);
                computeDisjointTerm(term1, predTrack, set);
                computeDisjointTerm(term2, predTrack, set);
                computeDisjointTerm(term3, predTrack, set)
            case BoolExp.Guard4(_, term1, term2, term3, term4) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term3), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term4), set);
                computeDisjointTerm(term1, predTrack, set);
                computeDisjointTerm(term2, predTrack, set);
                computeDisjointTerm(term3, predTrack, set);
                computeDisjointTerm(term4, predTrack, set)
            case BoolExp.Guard5(_, term1, term2, term3, term4, term5) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term3), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term5), set);
                computeDisjointTerm(term1, predTrack, set);
                computeDisjointTerm(term2, predTrack, set);
                computeDisjointTerm(term3, predTrack, set);
                computeDisjointTerm(term4, predTrack, set);
                computeDisjointTerm(term5, predTrack, set)
        }

        def unifyPredicates(relSym1: RelSym, relSym2: RelSym, set: MutDisjointSets[RamId, r]): Unit \ r =
            let arity = Ram.arityOf(relSym1);
            let id1 = Ram.toId(relSym1);
            let id2 = Ram.toId(relSym2);
            Vector.forEach(i -> {
                MutDisjointSets.makeSet(RamId.RelPos(id1, i), set);
                MutDisjointSets.makeSet(RamId.RelPos(id2, i), set);
                MutDisjointSets.union(RamId.RelPos(id1, i), RamId.RelPos(id2, i), set)
            }, Vector.range(0, arity))

        def unifyPredTypes(predSym: Int64, arity: Int32, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r =
            let fullSymbol = idToFullPredID(predSym, predTrack);
            let deltaSymbol = fullIDtoPredType(fullSymbol, PredType.Delta, predTrack);
            let newSymbol = fullIDtoPredType(fullSymbol, PredType.New, predTrack);
            Vector.forEach(i -> {
                MutDisjointSets.makeSet(RamId.RelPos(fullSymbol, i), set);
                MutDisjointSets.makeSet(RamId.RelPos(deltaSymbol, i), set);
                MutDisjointSets.union(RamId.RelPos(fullSymbol, i), RamId.RelPos(deltaSymbol, i), set)
            }, Vector.range(0, arity));
            Vector.forEach(i -> {
                MutDisjointSets.makeSet(RamId.RelPos(newSymbol, i), set);
                MutDisjointSets.union(RamId.RelPos(fullSymbol, i), RamId.RelPos(newSymbol, i), set)
            }, Vector.range(0, arity));
            ()

        def computeDisjointTerm(s: RamTerm, predTrack: Predicates, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RamTerm.Lit(_, id) =>
                MutDisjointSets.makeSet(id, set)
            case RamTerm.RowLoad(_, _, _) =>
                MutDisjointSets.makeSet(Ram.getTermRamId(s), set)
            case RamTerm.Meet(_, t1, (rv, relSym), id) => 
                computeDisjointTerm(t1, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                let id2 = Ram.getLatVarRamId(rv, relSym);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(id2, set);
                MutDisjointSets.makeSet(id, set);
                MutDisjointSets.union(id1, id, set);
                MutDisjointSets.union(id1, id2, set)
            case RamTerm.App1(_, t1, RamId.Id(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(RamId.InId(id, 0), set);
                MutDisjointSets.union(id1, RamId.InId(id, 0), set)
            case RamTerm.App2(_, t1, t2, RamId.Id(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                let id2 = Ram.getTermRamId(t2);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(id2, set);
                MutDisjointSets.makeSet(RamId.InId(id, 0), set);
                MutDisjointSets.makeSet(RamId.InId(id, 1), set);
                MutDisjointSets.union(id1, RamId.InId(id, 0), set);
                MutDisjointSets.union(id2, RamId.InId(id, 1), set)
            case RamTerm.App3(_, t1, t2, t3, RamId.Id(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                computeDisjointTerm(t3, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                let id2 = Ram.getTermRamId(t2);
                let id3 = Ram.getTermRamId(t3);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(id2, set);
                MutDisjointSets.makeSet(id3, set);
                MutDisjointSets.makeSet(RamId.InId(id, 0), set);
                MutDisjointSets.makeSet(RamId.InId(id, 1), set);
                MutDisjointSets.makeSet(RamId.InId(id, 2), set);
                MutDisjointSets.union(id1, RamId.InId(id, 0), set);
                MutDisjointSets.union(id2, RamId.InId(id, 1), set);
                MutDisjointSets.union(id3, RamId.InId(id, 2), set)
            case RamTerm.App4(_, t1, t2, t3, t4, RamId.Id(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                computeDisjointTerm(t3, predTrack, set);
                computeDisjointTerm(t4, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                let id2 = Ram.getTermRamId(t2);
                let id3 = Ram.getTermRamId(t3);
                let id4 = Ram.getTermRamId(t4);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(id2, set);
                MutDisjointSets.makeSet(id3, set);
                MutDisjointSets.makeSet(id4, set);
                MutDisjointSets.makeSet(RamId.InId(id, 0), set);
                MutDisjointSets.makeSet(RamId.InId(id, 1), set);
                MutDisjointSets.makeSet(RamId.InId(id, 2), set);
                MutDisjointSets.makeSet(RamId.InId(id, 3), set);
                MutDisjointSets.union(id1, RamId.InId(id, 0), set);
                MutDisjointSets.union(id2, RamId.InId(id, 1), set);
                MutDisjointSets.union(id3, RamId.InId(id, 2), set);
                MutDisjointSets.union(id4, RamId.InId(id, 3), set)
            case RamTerm.App5(_, t1, t2, t3, t4, t5, RamId.Id(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                computeDisjointTerm(t3, predTrack, set);
                computeDisjointTerm(t4, predTrack, set);
                computeDisjointTerm(t5, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                let id2 = Ram.getTermRamId(t2);
                let id3 = Ram.getTermRamId(t3);
                let id4 = Ram.getTermRamId(t4);
                let id5 = Ram.getTermRamId(t5);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(id2, set);
                MutDisjointSets.makeSet(id3, set);
                MutDisjointSets.makeSet(id4, set);
                MutDisjointSets.makeSet(id5, set);
                MutDisjointSets.makeSet(RamId.InId(id, 0), set);
                MutDisjointSets.makeSet(RamId.InId(id, 1), set);
                MutDisjointSets.makeSet(RamId.InId(id, 2), set);
                MutDisjointSets.makeSet(RamId.InId(id, 3), set);
                MutDisjointSets.makeSet(RamId.InId(id, 4), set);
                MutDisjointSets.union(id1, RamId.InId(id, 0), set);
                MutDisjointSets.union(id2, RamId.InId(id, 1), set);
                MutDisjointSets.union(id3, RamId.InId(id, 2), set);
                MutDisjointSets.union(id4, RamId.InId(id, 3), set);
                MutDisjointSets.union(id5, RamId.InId(id, 4), set)
            case _ => bug!("Unreachable")
        }

        @Internal
        def computeMappingStmt(s: RamStmt, predTrack: Predicates, set: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = match s {
            case RamStmt.Insert(rest) => computeMappingOp(rest, predTrack, set, map, counter)
            case RamStmt.MergeInto(rel1, rel2) =>
                insertIndexRelSym(rel1, set, map, counter);
                insertIndexRelSym(rel2, set, map, counter)
            case RamStmt.Swap(rel1, rel2) =>
                insertIndexRelSym(rel1, set, map, counter);
                insertIndexRelSym(rel2, set, map, counter)
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(x -> computeMappingStmt(x, predTrack, set, map, counter), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(x -> computeMappingStmt(x, predTrack, set, map, counter), stmts)
            case RamStmt.Until(bools, stmt) => 
                computeMappingStmt(stmt, predTrack, set, map, counter); 
                Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools)
            case RamStmt.Comment(_) => ()
            case RamStmt.EstimateJoinSize(_, _, _, _) => ()
        }

        def computeMappingOp(s: RelOp, predTrack: Predicates, set: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = 
            let recurse = x -> computeMappingOp(x, predTrack, set, map, counter);
            let insert = x -> insertIndex(x, set, map, counter);
            match s {
                case RelOp.Search(rv, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), rest) =>
                    Vector.forEach(i -> insert(RamId.TuplePos(rv, i)), Vector.range(0, arity));
                    Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity));
                    recurse(rest)
                case RelOp.Query(rv, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), bools, _, rest) =>
                    Vector.forEach(i -> insert(RamId.TuplePos(rv, i)), Vector.range(0, arity));
                    Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity));
                    Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools);
                    recurse(rest)
                case RelOp.Functional(RowVar.Named(id), _, inputTerms, rest, arity) => // equality on the input should be handled elsewhere.
                    Vector.forEach(i -> insert(RamId.TuplePos(RowVar.Named(id), i)), Vector.range(0, arity));
                    Vector.forEach(i -> insert(RamId.InId(id, i)), Vector.range(0, Vector.length(inputTerms)));
                    Vector.forEach(x -> computeMappingTerm(x, predTrack, set, map, counter), inputTerms);
                    recurse(rest)
                case RelOp.Project(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                    Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity));
                    Vector.forEach(x -> computeMappingTerm(x, predTrack, set, map, counter), terms)
                case RelOp.If(bools, rest) =>
                    recurse(rest);
                    Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools)
            }

        def computeMappingTerm(
            s: RamTerm, 
            predicates: Predicates, 
            set: MutDisjointSets[RamId, r], 
            map: MutMap[RamId, Int32, r], 
            counter: Counter[r]
        ): Unit \ r = 
            let insert = x -> insertIndex(x, set, map, counter);
            let computeMappingTermRec = x -> computeMappingTerm(x, predicates, set, map, counter);
            match s {
                case RamTerm.Lit(_, id) => insert(id)
                case RamTerm.RowLoad(_, _, _) => insert(getTermRamId(s))
                case RamTerm.Meet(_, t1, (rv, relSym), RamId.Id(id)) =>
                    computeMappingTermRec(t1);
                    insert(Ram.getLatVarRamId(rv, relSym));
                    insert(RamId.Id(id))
                case RamTerm.App1(_, t1, RamId.Id(id)) =>
                    computeMappingTermRec(t1);
                    insert(RamId.Id(id));
                    insert(RamId.InId(id, 0))
                case RamTerm.App2(_, t1, t2, RamId.Id(id)) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    insert(RamId.Id(id));
                    insert(RamId.InId(id, 0));
                    insert(RamId.InId(id, 1))
                case RamTerm.App3(_, t1, t2, t3, RamId.Id(id)) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3);
                    insert(RamId.Id(id));
                    insert(RamId.InId(id, 0));
                    insert(RamId.InId(id, 1));
                    insert(RamId.InId(id, 2))
                case RamTerm.App4(_, t1, t2, t3, t4, RamId.Id(id)) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3);
                    computeMappingTermRec(t4);
                    insert(RamId.Id(id));
                    insert(RamId.InId(id, 0));
                    insert(RamId.InId(id, 1));
                    insert(RamId.InId(id, 2));
                    insert(RamId.InId(id, 3))
                case RamTerm.App5(_, t1, t2, t3, t4, t5, RamId.Id(id)) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3);
                    computeMappingTermRec(t4);
                    computeMappingTermRec(t5);
                    insert(RamId.Id(id));
                    insert(RamId.InId(id, 0));
                    insert(RamId.InId(id, 1));
                    insert(RamId.InId(id, 2));
                    insert(RamId.InId(id, 3));
                    insert(RamId.InId(id, 4))
                case _ => bug!("Unreachable")
            }

        def computeMappingBool(
            s: BoolExp, 
            predicates: Predicates, 
            set: MutDisjointSets[RamId, r], 
            map: MutMap[RamId, Int32, r], 
            counter: Counter[r]
        ): Unit \ r = 
            let insert = x -> insertIndex(x, set, map, counter);
            let computeMappingTermRec = x -> computeMappingTerm(x, predicates, set, map, counter);
            match s {
                case BoolExp.Not(boolExp) => computeMappingBool(boolExp, predicates, set, map, counter)
                case BoolExp.IsEmpty(_) => ()
                case BoolExp.NotMemberOf(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                    Vector.forEach(x -> computeMappingTermRec(x), terms);
                    Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity))
                case BoolExp.Eq(t1, t2) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2)
                case BoolExp.NotBot(t1, _, _) =>
                    computeMappingTermRec(t1)
                case BoolExp.Leq(_, _, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                    insert(RamId.RelPos(predSym, arity - 1))
                case BoolExp.Guard1(_, t1) =>
                    computeMappingTermRec(t1)
                case BoolExp.Guard2(_, t1, t2) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2)
                case BoolExp.Guard3(_, t1, t2, t3) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3)
                case BoolExp.Guard4(_, t1, t2, t3, t4) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3);
                    computeMappingTermRec(t4)
                case BoolExp.Guard5(_, t1, t2, t3, t4, t5) =>
                    computeMappingTermRec(t1);
                    computeMappingTermRec(t2);
                    computeMappingTermRec(t3);
                    computeMappingTermRec(t4);
                    computeMappingTermRec(t5)
            }

        def insertIndexRelSym(relSym: RelSym, disjoint: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r =
            let arity = Ram.arityOf(relSym);
            let id = Ram.toId(relSym);
            Vector.forEach(i -> {
                insertIndex(RamId.RelPos(id, i), disjoint, map, counter)
            }, Vector.range(0, arity))


        def insertIndex(id: RamId, disjoint: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = 
            def unwrap(v: Option[RamId]): RamId = match v {
                case Some(x) => x
                case None => bug!("RamID not in disjoint datastructure: ${id}\n")
            };
            let repID = unwrap(MutDisjointSets.find(id, disjoint)); 
            match MutMap.get(repID, map) {
                case Some(v) => MutMap.put(id, v, map)
                case None => 
                    let newID = Counter.getNewID(counter);
                    MutMap.put(id, newID, map);
                    MutMap.put(repID, newID, map)
            }
    }

    def unwrap(v: Option[a]): a = match v {
        case Some(x) => x
        case None => bug!("Marshall error")
    }
}