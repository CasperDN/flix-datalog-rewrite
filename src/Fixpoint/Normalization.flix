///
/// The purpose of this file is to map boxed constants to Int64 
/// since the indices on relations work on Int64 due to the lower
/// complexity of working with integers
///
mod Fixpoint.Boxing {
    use Fixpoint.Boxed
    use Fixpoint.Boxable
    use Fixpoint.Ast.Ram
    use Fixpoint.Ast.Ram.{RamId, RamStmt, RelOp, RamTerm, BoolExp, RelSym}
    use Fixpoint.Ast.Datalog.{Datalog}
    use Fixpoint.Boxed.{BoxedBool, BoxedChar, BoxedInt8, BoxedInt16, BoxedInt32, BoxedInt64, BoxedFloat32, BoxedFloat64, BoxedObject}
    use Fixpoint.Boxing.Boxing
    use Fixpoint.Ast.Ram.{RelSym, RamProgram}
    use Fixpoint.Ast.Shared.{PredSym, isRelational, Denotation}
    use RelSymTypeInfo.{setType, getType, RealType}
    import java.lang.{Float, Double, Object, Character}


    

    // Could just as well be a list

    mod RelSymTypeInfo {
        pub enum RealType {
            case Unknown
            case Bool
            case Char
            case Int8
            case Int16
            case Int32
            case Int64
            case Float32
            case Float64
            case Object
        }

        pub type alias RelSymTypeInfo[r: Eff] = Array[RealType, r]

        pub def setType(t: RealType, index: Int32, symInfo: RelSymTypeInfo[r]): Unit \ r = Array.put(t, index, symInfo)

        pub def getType(index: Int32, symInfo: RelSymTypeInfo[r]): RealType \ r = Array.get(index, symInfo)
    }

    // It would be nice if MutMap could take a comparison
    // (List of Boxed objects, [RelSym->IndexInTyple->BoxedObject->Int64], mapping fram RelSym and index to RealType)
    pub type alias Boxing[r: Region] = (Vector[MutList[Boxed, r]], Vector[MutMap[Boxed, Int64, r]], RelSymTypeInfo.RelSymTypeInfo[r])

    pub type alias RamIdToMarshal = Map[RamId, Int32]

    pub def initialize(rc: Region[r], r: RamProgram): (Boxing[r], RamIdToMarshal) \ r =
        let mapping = Equality.computeMapping(r);
        (initializeInternal(rc, r, mapping), mapping)

    def initializeInternal(rc: Region[r], r: RamProgram, map: RamIdToMarshal): Boxing[r] \ r =
        let max = 1 + snd(Option.getWithDefault((RamId.Id(-1), -1), Map.maximumValue(map)));
        let intToBox = Vector.init(_ -> MutList.empty(rc), max);
        let boxToInt = Vector.init(_ -> MutMap.empty(rc), max);
        let posToIndex = Array.empty(rc, max);
        let info = (intToBox, boxToInt, posToIndex);
        let relSyms = Ram.collectRelSym(r);
        // Add bot first to make sure it corresponds to 0.
        List.filter(match RelSym.Symbol(_, _, den) -> not isRelational(den), relSyms) |>
            List.forEach(x -> match x {
                case RelSym.Symbol(PredSym.PredSym(_, index), arity, Denotation.Latticenal(bot, _, _, _)) => 
                    debox(bot, unwrap(Map.get(RamId.RelPos(index, arity), map)), info); ()
                case _ => bug!("Should have been filtered out")
        });
        (intToBox, boxToInt, posToIndex)

    def deMarshalObject(value: Int64, index: Int32, info: Boxing[r]): Boxed \ r = {
        let (objectList, _, _) = info;
        // TODO: remove nth.
        unwrap(MutList.nth(unwrap(Int64.tryToInt32(value)), Vector.get(index, objectList)))
        // unchecked_cast(fst(info).get(unwrap(Int64.tryToInt32(index))) as _ \ {})
    }

    // We could Box the object and thus have a Boxed as input and be able to sort them?
    def marshallObject(box: Boxed, index: Int32, info: Boxing[r]): Int64 \ r = {
        let (objectLists, vecObjectMap, _) = info;
        let objectList = Vector.get(index, objectLists);
        let objectMap = Vector.get(index, vecObjectMap);
        let map = objectMap;
        match MutMap.get(box, map) {
            case Some(id)   => id
            case None       => 
                let id = getNextIndex(objectList);
                MutList.insert(box, id, objectList); // TODO: Not thread safe
                Int32.toInt64(id)
        }
    }

    // TODO: Not thread safe. Apply locking (or use an AtomicInteger). Locking is needed for MutList anyway.
    def getNextIndex(objectList: MutList[Boxed, r]): Int32 \ r = {
        // let (objectList, _, _) = info;
        MutList.length(objectList)
    }


    pub def debox(box: Boxed, index: Int32, info: Boxing[r]): Int64 \ r =
    let (_, _, symInfo) = info;
    match box {
        case BoxedBool(x)       => setType(RealType.Bool, index, symInfo); if (x) 1i64 else 0i64
        case BoxedChar(x)       => setType(RealType.Char, index, symInfo); Int32.toInt64(Char.toBmpCodePoint(x))
        case BoxedInt8(x)       => setType(RealType.Int8, index, symInfo); Int8.toInt64(x)
        case BoxedInt16(x)      => setType(RealType.Int16, index, symInfo); Int16.toInt64(x)
        case BoxedInt32(x)      => setType(RealType.Int32, index, symInfo); Int32.toInt64(x)
        case BoxedInt64(x)      => setType(RealType.Int64, index, symInfo); x
        case BoxedFloat32(x)    => setType(RealType.Float32, index, symInfo); Int32.toInt64(Float.floatToRawIntBits(Float32.valueOf(x).floatValue()))
        case BoxedFloat64(x)    => setType(RealType.Float64, index, symInfo); Double.doubleToRawLongBits(Float64.valueOf(x).doubleValue())
        case BoxedObject(_, _)  => setType(RealType.Object, index, symInfo); marshallObject(box, index, info) // We remap to low, so only goes wrong when dealing with more than 2^32 different RelSyms
    }

    pub def rebox(v: Int64, index: Int32, info: Boxing[r]): Boxed \ r = 
        let (_, _, symInfo) = info;
        match getType(index, symInfo) {
            case RealType.Bool      => Boxed.BoxedBool(not(v == 0i64))
            case RealType.Char      => BoxedChar(unchecked_cast(Array.get(0, Character.toChars(unwrap(Int64.tryToInt32(v)))) as _ \ {}))
            case RealType.Int8      => BoxedInt8(unwrap(Int64.tryToInt8(v)))
            case RealType.Int16     => BoxedInt16(unwrap(Int64.tryToInt16(v)))
            case RealType.Int32     => BoxedInt32(unwrap(Int64.tryToInt32(v)))
            case RealType.Int64     => BoxedInt64(v)
            case RealType.Float32   => BoxedFloat32(Float.intBitsToFloat(unwrap(Int64.tryToInt32(v))))
            case RealType.Float64   => BoxedFloat64(Double.longBitsToDouble(v))
            case RealType.Object    => deMarshalObject(v, index, info)
            case RealType.Unknown   => bug!("Unormalizing value, which has never been normalized")
        }

    // pub def reboxByLatticeElem(v: Int64, index: Int32, info: Boxing[r]): Boxed \ r = 
    //     let (_, _, symInfo) = info;
    //     match getType(index, symInfo) {
    //         case RealType.Bool      => Boxed.BoxedBool(not(v == 0i64))
    //         case RealType.Char      => BoxedChar(unchecked_cast(Array.get(0, Character.toChars(unwrap(Int64.tryToInt32(v)))) as _ \ {}))
    //         case RealType.Int8      => BoxedInt8(unwrap(Int64.tryToInt8(v)))
    //         case RealType.Int16     => BoxedInt16(unwrap(Int64.tryToInt16(v)))
    //         case RealType.Int32     => BoxedInt32(unwrap(Int64.tryToInt32(v)))
    //         case RealType.Int64     => BoxedInt64(v)
    //         case RealType.Float32   => BoxedFloat32(Float.intBitsToFloat(unwrap(Int64.tryToInt32(v))))
    //         case RealType.Float64   => BoxedFloat64(Double.longBitsToDouble(v))
    //         case RealType.Object    => deMarshalObject(v, info)
    //         case RealType.Unknown   => bug!("Unormalizing value, which has never been normalized")
    //     }


    // Compute equality for the terms, deciding what can safely be stored together. Might miss some, but only a problem for objects.
    // Equality is on the full symbols.
    mod Equality {
        use Fixpoint.Ast.Ram.getTermRamId
        use Fixpoint.Ast.Ram
        use Fixpoint.Ast.Ram.{RamId, RamStmt, RelOp, RamTerm, BoolExp, RamProgram, toPredID, TupleVar}
        use PredTrack.PredSymMapInternal
        use Fixpoint.Ast.Ram.{RelSym, RamProgram}
        use Fixpoint.Ast.Shared.PredSym
        use Fixpoint.Counter
        use Fixpoint.Counter.Counter

        pub def computeMapping(d: RamProgram): Map[RamId, Int32] = region rc {
            let disjointSet = MutDisjointSets.empty(rc);
            let RamProgram.Program(s, facts, predTrack, _) = d;
            computeDisjointStmt(s, predTrack, disjointSet);
            Map.forEach(match RelSym.Symbol(PredSym.PredSym(_, id), arity, _) -> _ -> {
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.RelPos(id, i), disjointSet), Vector.range(0, arity))
            }, facts);
            let mutMap = MutMap.empty(rc);
            let counter = Counter.empty(rc);
            Map.forEach(match RelSym.Symbol(PredSym.PredSym(_, id), arity, _) -> _ -> {
                Vector.forEach(i -> insertIndex(RamId.RelPos(id, i), disjointSet, mutMap, counter), Vector.range(0, arity))
            }, facts);            
            computeMappingStmt(s, predTrack, disjointSet, mutMap, counter);
            MutMap.toMap(mutMap)
            // let _ = "";
            // Map.empty()
        }

        // pub def computeDisjointSet(d: RamProgram): Unit = region rc {
        //     let disjoint = MutDisjointSets.empty(rc);
        //     let RamProgram.Program(s, _, predTrack, _) = d;
        //     computeDisjointStmt(s, predTrack, disjoint);
        //     // disjoint
        //     ()
        // }

        def computeDisjointStmt(s: RamStmt, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RamStmt.Insert(rest) => computeDisjointOp(rest, predTrack, set)
            case RamStmt.Merge(_, _) => ()
            case RamStmt.Swap(_, _) => ()
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(x -> computeDisjointStmt(x, predTrack, set), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(x -> computeDisjointStmt(x, predTrack, set), stmts)
            case RamStmt.Until(bools, stmt) => computeDisjointStmt(stmt, predTrack, set); Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools)
            case RamStmt.Comment(_) => ()
        }

        def computeDisjointOp(s: RelOp, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RelOp.Search(TupleVar.Named(id), RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), rest) =>
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.TuplePos(id, i), set), Vector.range(0, arity));
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                Vector.forEach(i -> MutDisjointSets.union(RamId.TuplePos(id, i), RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                unifyPredTypes(predSym, arity, predTrack, set);
                computeDisjointOp(rest, predTrack, set)
            case RelOp.SearchWithIndex(TupleVar.Named(id), RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), bools, _, rest) =>
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.TuplePos(id, i), set), Vector.range(0, arity));
                Vector.forEach(i -> MutDisjointSets.makeSet(RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                Vector.forEach(i -> MutDisjointSets.union(RamId.TuplePos(id, i), RamId.RelPos(predSym, i), set), Vector.range(0, arity));
                unifyPredTypes(predSym, arity, predTrack, set);
                Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools);
                computeDisjointOp(rest, predTrack, set)
            case RelOp.Functional(TupleVar.Named(id), _, inputTerms, rest, _) => // equality on the input should be handled elsewhere.
                Vector.forEachWithIndex(i -> curTerm -> {
                    let termID = Ram.getTermRamId(curTerm);
                    MutDisjointSets.union(RamId.InID(id, i), termID, set);
                    computeDisjointTerm(curTerm, predTrack, set)
                }, inputTerms);
                computeDisjointOp(rest, predTrack, set)
            case RelOp.Project(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                unifyPredTypes(predSym, arity, predTrack, set);
                // Vector.forEach(i -> MutDisjointSets.makeSet(RamId.RelPos(fullSym, i), set), Vector.range(0, Vector.length(terms)));
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

        def computeDisjointBool(s: BoolExp, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case BoolExp.IsEmpty(_) => ()
            case BoolExp.NotMemberOf(terms, RelSym.Symbol(PredSym.PredSym(_, id), _, _)) =>
                Vector.forEach(term -> computeDisjointTerm(term, predTrack, set), terms);
                Vector.forEachWithIndex(i -> term -> {
                    MutDisjointSets.makeSet(Ram.getTermRamId(term), set);
                    MutDisjointSets.makeSet(RamId.RelPos(id, i), set);
                    MutDisjointSets.union(Ram.getTermRamId(term), RamId.RelPos(id, i), set)
                }, terms)
            case BoolExp.Eq(term1, term2) =>
                computeDisjointTerm(term1, predTrack, set);
                computeDisjointTerm(term2, predTrack, set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.union(Ram.getTermRamId(term1), Ram.getTermRamId(term2), set)
            case BoolExp.Leq(_, term1, term2) =>
                computeDisjointTerm(term1, predTrack, set);
                computeDisjointTerm(term2, predTrack, set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term1), set);
                MutDisjointSets.makeSet(Ram.getTermRamId(term2), set);
                MutDisjointSets.union(Ram.getTermRamId(term1), Ram.getTermRamId(term2), set)
            case BoolExp.Guard0(_) => ()
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

        def unifyPredTypes(predSym: Int64, arity: Int32, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r]): Unit \ r =
            let fullSymbol = PredTrack.idToFullPredID(predSym, predTrack);
            let deltaSymbol = PredTrack.fullIDtoPredType(fullSymbol, PredTrack.PredType.Delta, predTrack);
            let newSymbol = PredTrack.fullIDtoPredType(fullSymbol, PredTrack.PredType.New, predTrack);
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

        def computeDisjointTerm(s: RamTerm, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r]): Unit \ r = match s {
            case RamTerm.Lit(_, _) => ()
            case RamTerm.RowLoad(_, _, _) => ()
            // case RamTerm.LoadLatVar(_, _, _) => ()
            case RamTerm.Meet(_, t1, t2, RamId.Id(id)) => 
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                let id2 = Ram.getTermRamId(t2);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(RamId.TuplePos(id, 0), set);
                MutDisjointSets.makeSet(RamId.TuplePos(id, 1), set);
                MutDisjointSets.union(id1, RamId.TuplePos(id, 0), set);
                MutDisjointSets.union(id2, RamId.TuplePos(id, 1), set);
                MutDisjointSets.union(id1, id2, set)
            case RamTerm.App0(_, _) => ()
            case RamTerm.App1(_, t1, RamId.Id(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(RamId.InID(id, 0), set);
                MutDisjointSets.union(id1, RamId.InID(id, 0), set)
            case RamTerm.App2(_, t1, t2, RamId.Id(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                let id1 = Ram.getTermRamId(t1);
                let id2 = Ram.getTermRamId(t2);
                MutDisjointSets.makeSet(id1, set);
                MutDisjointSets.makeSet(id2, set);
                MutDisjointSets.makeSet(RamId.InID(id, 0), set);
                MutDisjointSets.makeSet(RamId.InID(id, 1), set);
                MutDisjointSets.union(id1, RamId.InID(id, 0), set);
                MutDisjointSets.union(id2, RamId.InID(id, 1), set)
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
                MutDisjointSets.makeSet(RamId.InID(id, 0), set);
                MutDisjointSets.makeSet(RamId.InID(id, 1), set);
                MutDisjointSets.makeSet(RamId.InID(id, 2), set);
                MutDisjointSets.union(id1, RamId.InID(id, 0), set);
                MutDisjointSets.union(id2, RamId.InID(id, 1), set);
                MutDisjointSets.union(id3, RamId.InID(id, 2), set)
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
                MutDisjointSets.makeSet(RamId.InID(id, 0), set);
                MutDisjointSets.makeSet(RamId.InID(id, 1), set);
                MutDisjointSets.makeSet(RamId.InID(id, 2), set);
                MutDisjointSets.makeSet(RamId.InID(id, 3), set);
                MutDisjointSets.union(id1, RamId.InID(id, 0), set);
                MutDisjointSets.union(id2, RamId.InID(id, 1), set);
                MutDisjointSets.union(id3, RamId.InID(id, 2), set);
                MutDisjointSets.union(id4, RamId.InID(id, 3), set)
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
                MutDisjointSets.makeSet(RamId.InID(id, 0), set);
                MutDisjointSets.makeSet(RamId.InID(id, 1), set);
                MutDisjointSets.makeSet(RamId.InID(id, 2), set);
                MutDisjointSets.makeSet(RamId.InID(id, 3), set);
                MutDisjointSets.makeSet(RamId.InID(id, 4), set);
                MutDisjointSets.union(id1, RamId.InID(id, 0), set);
                MutDisjointSets.union(id2, RamId.InID(id, 1), set);
                MutDisjointSets.union(id3, RamId.InID(id, 2), set);
                MutDisjointSets.union(id4, RamId.InID(id, 3), set);
                MutDisjointSets.union(id5, RamId.InID(id, 4), set)
            case _ => bug!("Unreachable")
        }

        @Internal
        def computeMappingStmt(s: RamStmt, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = match s {
            case RamStmt.Insert(rest) => computeMappingOp(rest, predTrack, set, map, counter)
            case RamStmt.Merge(_, _) => ()
            case RamStmt.Swap(_, _) => ()
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(x -> computeMappingStmt(x, predTrack, set, map, counter), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(x -> computeMappingStmt(x, predTrack, set, map, counter), stmts)
            case RamStmt.Until(bools, stmt) => 
                computeMappingStmt(stmt, predTrack, set, map, counter); 
                Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools)
            case RamStmt.Comment(_) => ()
        }


        def computeMappingOp(s: RelOp, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = 
        let recurse = x -> computeMappingOp(x, predTrack, set, map, counter);
        let insert = x -> insertIndex(x, set, map, counter);
        match s {
            case RelOp.Search(_, _, rest) => recurse(rest)
            case RelOp.SearchWithIndex(TupleVar.Named(id), RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), bools, _, rest) =>
                Vector.forEach(i -> insert(RamId.TuplePos(id, i)), Vector.range(0, arity));
                Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity));
                Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools);
                recurse(rest)
            case RelOp.Functional(TupleVar.Named(id), _, inputTerms, rest, arity) => // equality on the input should be handled elsewhere.
                Vector.forEach(i -> insert(RamId.InID(id, i)), Vector.range(0, arity));
                Vector.forEach(i -> insert(RamId.TuplePos(id, i)), Vector.range(0, Vector.length(inputTerms)));
                Vector.forEach(x -> computeMappingTerm(x, predTrack, set, map, counter), inputTerms);
                recurse(rest)
                // Vector.forEachWithIndex(i -> curTerm -> {
                //     let termID = Ram.getTermRamId(curTerm);
                //     MutDisjointSets.union(RamId.FunctionalOutID(outID, i), termID, set); // Possibly not needed as it should be covered by equality
                //     computeDisjointTerm(curTerm, predTrack, set)
                //     // match curTerm {
                //     //     case RamTerm.RowLoad(varr, index, ramID) => MutDisjointSets.makeSet(ramID, set); MutDisjointSets.makeSet((varr, index), set)
                //     //     case _ => ()
                //     // }
                // }, inputTerms);
                // computeDisjointOp(rest, predTrack, set);
                // ??? // I think it works, so this should be removed
            case RelOp.Project(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity));
                Vector.forEach(x -> computeMappingTerm(x, predTrack, set, map, counter), terms)
            case RelOp.If(bools, rest) =>
                recurse(rest);
                Vector.forEach(x -> computeMappingBool(x, predTrack, set, map, counter), bools)
        }


        def computeMappingTerm(s: RamTerm, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = 
        let insert = x -> insertIndex(x, set, map, counter);
        let recurse = x -> computeMappingTerm(x, predTrack, set, map, counter);
        match s {
            case RamTerm.Lit(_, id) => insert(id)
            case RamTerm.RowLoad(_, _, _) => insert(getTermRamId(s))
            // case RamTerm.LoadLatVar(_, _, id) => insert(id)
            case RamTerm.Meet(_, t1, t2, RamId.Id(id)) =>
                recurse(t1);
                recurse(t2);
                insert(RamId.Id(id));
                insert(RamId.InID(id, 0));
                insert(RamId.InID(id, 1))
            case RamTerm.App0(_, id) => insert(id)
            case RamTerm.App1(_, t1, RamId.Id(id)) =>
                recurse(t1);
                insert(RamId.Id(id));
                insert(RamId.InID(id, 0))
            case RamTerm.App2(_, t1, t2, RamId.Id(id)) =>
                recurse(t1);
                recurse(t2);
                insert(RamId.Id(id));
                insert(RamId.InID(id, 0));
                insert(RamId.InID(id, 1))
            case RamTerm.App3(_, t1, t2, t3, RamId.Id(id)) =>
                recurse(t1);
                recurse(t2);
                recurse(t3);
                insert(RamId.Id(id));
                insert(RamId.InID(id, 0));
                insert(RamId.InID(id, 1));
                insert(RamId.InID(id, 2))
            case RamTerm.App4(_, t1, t2, t3, t4, RamId.Id(id)) =>
                recurse(t1);
                recurse(t2);
                recurse(t3);
                recurse(t4);
                insert(RamId.Id(id));
                insert(RamId.InID(id, 0));
                insert(RamId.InID(id, 1));
                insert(RamId.InID(id, 2));
                insert(RamId.InID(id, 3))
            case RamTerm.App5(_, t1, t2, t3, t4, t5, RamId.Id(id)) =>
                recurse(t1);
                recurse(t2);
                recurse(t3);
                recurse(t4);
                recurse(t5);
                insert(RamId.Id(id));
                insert(RamId.InID(id, 0));
                insert(RamId.InID(id, 1));
                insert(RamId.InID(id, 2));
                insert(RamId.InID(id, 3));
                insert(RamId.InID(id, 4))
            case _ => bug!("Unreachable")
        }

        def computeMappingBool(s: BoolExp, predTrack: PredSymMapInternal, set: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = 
        let insert = x -> insertIndex(x, set, map, counter);
        let recurseOnTerm = x -> computeMappingTerm(x, predTrack, set, map, counter);
        match s {
            case BoolExp.IsEmpty(_) => ()
            case BoolExp.NotMemberOf(terms, RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _)) =>
                Vector.forEach(x -> recurseOnTerm(x), terms);
                Vector.forEach(i -> insert(RamId.RelPos(predSym, i)), Vector.range(0, arity))
            case BoolExp.Eq(t1, t2) =>
                recurseOnTerm(t1);
                recurseOnTerm(t2)
            case BoolExp.Leq(_, t1, t2) =>
                recurseOnTerm(t1);
                recurseOnTerm(t2)
            case BoolExp.Guard0(_) => ()
            case BoolExp.Guard1(_, t1) =>
                recurseOnTerm(t1)
            case BoolExp.Guard2(_, t1, t2) =>
                recurseOnTerm(t1);
                recurseOnTerm(t2)
            case BoolExp.Guard3(_, t1, t2, t3) =>
                recurseOnTerm(t1);
                recurseOnTerm(t2);
                recurseOnTerm(t3)
            case BoolExp.Guard4(_, t1, t2, t3, t4) =>
                recurseOnTerm(t1);
                recurseOnTerm(t2);
                recurseOnTerm(t3);
                recurseOnTerm(t4)
            case BoolExp.Guard5(_, t1, t2, t3, t4, t5) =>
                recurseOnTerm(t1);
                recurseOnTerm(t2);
                recurseOnTerm(t3);
                recurseOnTerm(t4);
                recurseOnTerm(t5)

        }
            // case RamTerm.Lit(_, id) => insert(id)
            // case RamTerm.RowLoad(_, _, _, id) => insert(id)
            // case RamTerm.LoadLatVar(_, _, id) => insert(id)
            // case RamTerm.Meet(_, t1, t2, RamId.Id(id)) =>
            //     recurse(t1);
            //     recurse(t2);
            //     insert(RamId.Id(id));
            //     insert(RamId.InID(id, 0));
            //     insert(RamId.InID(id, 1))
            // case RamTerm.App0(_, id) => insert(id)
            // case RamTerm.App1(_, t1, RamId.Id(id)) =>
            //     recurse(t1);
            //     insert(RamId.Id(id));
            //     insert(RamId.InID(id, 0))
            // case RamTerm.App2(_, t1, t2, RamId.Id(id)) =>
            //     recurse(t1);
            //     recurse(t2);
            //     insert(RamId.Id(id));
            //     insert(RamId.InID(id, 0));
            //     insert(RamId.InID(id, 1))
            // case RamTerm.App3(_, t1, t2, t3, RamId.Id(id)) =>
            //     recurse(t1);
            //     recurse(t2);
            //     recurse(t3);
            //     insert(RamId.Id(id));
            //     insert(RamId.InID(id, 0));
            //     insert(RamId.InID(id, 1));
            //     insert(RamId.InID(id, 2))
            // case RamTerm.App4(_, t1, t2, t3, t4, RamId.Id(id)) =>
            //     recurse(t1);
            //     recurse(t2);
            //     recurse(t3);
            //     recurse(t4);
            //     insert(RamId.Id(id));
            //     insert(RamId.InID(id, 0));
            //     insert(RamId.InID(id, 1));
            //     insert(RamId.InID(id, 2));
            //     insert(RamId.InID(id, 3))
            // case RamTerm.App5(_, t1, t2, t3, t4, t5, RamId.Id(id)) =>
            //     recurse(t1);
            //     recurse(t2);
            //     recurse(t3);
            //     recurse(t4);
            //     recurse(t5);
            //     insert(RamId.Id(id));
            //     insert(RamId.InID(id, 0));
            //     insert(RamId.InID(id, 1));
            //     insert(RamId.InID(id, 2));
            //     insert(RamId.InID(id, 3));
            //     insert(RamId.InID(id, 4))
            // case _ => bug!("Unreachable")
        

        def insertIndex(id: RamId, disjoint: MutDisjointSets[RamId, r], map: MutMap[RamId, Int32, r], counter: Counter[r]): Unit \ r = 
            def unwrap(v: Option[RamId]): RamId = match v {
                case Some(x) => x
                case None => bug!("Primitive value somehow exceeded the size it should fit into: ${Debug.stringify(id)}\n")
            };
            let repID = unwrap(MutDisjointSets.find(id, disjoint)); match MutMap.get(repID, map) {
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