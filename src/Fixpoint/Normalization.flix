///
/// The purpose of this file is to map boxed constants to Int64 
/// since the indices on relations work on Int64 due to the lower
/// complexity of working with integers
///
mod Fixpoint.Normalization {
    use Fixpoint.Boxed
    use Fixpoint.Boxable
    use Fixpoint.Ast.AugmentedRam
    use Fixpoint.Ast.AugmentedRam.{RamID, RamStmt, RelOp, RamTerm, BoolExp}
    use Fixpoint.Ast.Datalog.{Datalog}
    use Fixpoint.Boxed.{BoxedBool, BoxedChar, BoxedInt8, BoxedInt16, BoxedInt32, BoxedInt64, BoxedFloat32, BoxedFloat64, BoxedObject}
    use Fixpoint.Normalization.ObjectMarshallingInfo
    use Fixpoint.Ast.AugmentedRam.{RelSym, AugmentedProgram}
    use Fixpoint.Ast.Shared.PredSym
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

        pub type alias RelSymTypeInfo[r: Eff] = Map[Int64, Array[RealType, r]]
        
        pub def setType(t: RealType, predSymIndex: Int64, index: Int32, symInfo: RelSymTypeInfo[r]): Unit \ r = match Map.get(predSymIndex, symInfo) {
            case Some(v)    => Array.put(t, index, v)
            case None       => bug!("")
        }

        pub def getType(predSymIndex: Int64, index: Int32, symInfo: RelSymTypeInfo[r]): RealType \ r = match Map.get(predSymIndex, symInfo) {
            case Some(v)    => Array.get(index, v)
            case None       => bug!("")
        }
    }

    // It would be nice if MutMap could take a comparison
    // (List of Boxed objects, [RelSym->IndexInTyple->BoxedObject->Int64], mapping fram RelSym and index to RealType)
    pub type alias ObjectMarshallingInfo[r: Eff] = (MutList[Boxed, r], Vector[Vector[MutMap[Boxed, Int64, r]]], RelSymTypeInfo.RelSymTypeInfo[r])

    pub def initialize(r: AugmentedProgram, rc: Region[r]): ObjectMarshallingInfo[r] = ???

    def deMarshalObject(index: Int64, info: ObjectMarshallingInfo[r]): Boxed \ r = {
        let (objectList, _, _) = info;
        unwrap(MutList.nth(unwrap(Int64.tryToInt32(index)), objectList))
        // unchecked_cast(fst(info).get(unwrap(Int64.tryToInt32(index))) as _ \ {})
    }

    // We could Box the object and thus have a Boxed as input and be able to sort them?
    def marshallObject(box: Boxed, info: ObjectMarshallingInfo[r], relSymIndex: Int32, index: Int32): Int64 \ r = {
        let (objectList, vecObjectMap, _) = info;
        let objectMap = Vector.get(index, Vector.get(relSymIndex, vecObjectMap));
        let map = objectMap;
        // let cmp = (o1, o2) -> Order.compare(unchecked_cast(o1 as a), unchecked_cast(o2 as a));
        // let box = Boxed.BoxedObject(unchecked_cast(x as Object), cmp);
        // let obj = match box {
        //     case BoxedObject(x, _) => x
        //     case _ => bug!("Marshalling non-object value")
        // };
        // let max = 
        match MutMap.get(box, map) {
            case Some(id)   => id
            case None       => 
                let id = getNextIndex(info);
                MutList.insert(box, id, objectList);
                // let id_ = unchecked_cast({fst(info).add(id, unchecked_cast(x as Object)); id} as _ \ {});
                Int32.toInt64(id)
        }
        // let index = MutMap.getOrElsePut(box, getNextIndex(info), map);
        // ???
        // MutMap.get()
    }

    // TODO: Not thread safe. Apply locking (or use an AtomicInteger). Locking is needed for MutList anyway.
    def getNextIndex(info: ObjectMarshallingInfo[r]): Int32 \ r = {
        let (objectList, _, _) = info;
        MutList.length(objectList)
    }


    pub def normalizeBox(box: Boxed, predSymIndex: Int64, index: Int32, info: ObjectMarshallingInfo[r]): Int64 \ r =
    let (_, _, symInfo) = info;
    match box {
        case BoxedBool(x)       => setType(RealType.Bool, predSymIndex, index, symInfo); if (x) 1i64 else 0i64
        case BoxedChar(x)       => setType(RealType.Char, predSymIndex, index, symInfo); Int32.toInt64(Char.toBmpCodePoint(x)) // TODO: Confirm with Magnus
        case BoxedInt8(x)       => setType(RealType.Int8, predSymIndex, index, symInfo); Int8.toInt64(x)
        case BoxedInt16(x)      => setType(RealType.Int16, predSymIndex, index, symInfo); Int16.toInt64(x)
        case BoxedInt32(x)      => setType(RealType.Int32, predSymIndex, index, symInfo); Int32.toInt64(x)
        case BoxedInt64(x)      => setType(RealType.Int64, predSymIndex, index, symInfo); x
        case BoxedFloat32(x)    => setType(RealType.Float32, predSymIndex, index, symInfo); Int32.toInt64(Float.floatToRawIntBits(Float32.valueOf(x).floatValue()))
        case BoxedFloat64(x)    => setType(RealType.Float64, predSymIndex, index, symInfo); Double.doubleToRawLongBits(Float64.valueOf(x).doubleValue())
        case BoxedObject(_, _)  => setType(RealType.Object, predSymIndex, index, symInfo); marshallObject(box, info, unwrap(Int64.tryToInt32(predSymIndex)), index) // We remap to low, so only goes wrong when dealing with more than 2^32 different RelSyms
    }

    // pub def normalizeReal(value: v, info: ObjectMarshallingInfo[r]): Int64 \ r with Order[v] = normalizeBox(Boxable.box(value), info)

    // pub def getRealType(r: RelSym, index: Int32, info: ObjectMarshallingInfo[r]): RealType =
    //     let (_, _, x) = info;
    //     ???
        
        // ???
        // RealType.Bool

    pub def unNormalizeReal(v: Int64, predSymIndex: Int64, index: Int32, info: ObjectMarshallingInfo[r]): Boxed \ r = 
        let (_, _, symInfo) = info;
        match getType(predSymIndex, index, symInfo) {
            case RealType.Bool      => Boxed.BoxedBool(not(v == 0i64))
            case RealType.Char      => BoxedChar(unchecked_cast(Array.get(0, Character.toChars(unwrap(Int64.tryToInt32(v)))) as _ \ {}))
            case RealType.Int8      => BoxedInt8(unwrap(Int64.tryToInt8(v)))
            case RealType.Int16     => BoxedInt16(unwrap(Int64.tryToInt16(v)))
            case RealType.Int32     => BoxedInt32(unwrap(Int64.tryToInt32(v)))
            case RealType.Int64     => BoxedInt64(v)
            case RealType.Float32   => BoxedFloat32(Float.intBitsToFloat(unwrap(Int64.tryToInt32(v))))
            case RealType.Float64   => BoxedFloat64(Double.longBitsToDouble(v))
            case RealType.Object    => deMarshalObject(v, info)
            case RealType.Unknown   => bug!("Unormalizing value, which has never been normalized")
        }

    // Compute equality for the terms, deciding what can safely be stored together. Might miss some, but only a problem for objects.
    // Equality is on the full symbols.
    mod Equality {
        use Fixpoint.Ast.AugmentedRam
        use Fixpoint.Ast.AugmentedRam.{RamID, RamStmt, RelOp, RamTerm, BoolExp, AugmentedProgram, toPredID, TupleVar}
        use PredTrack.PredSymMapInternal
        use Fixpoint.Ast.AugmentedRam.{RelSym, AugmentedProgram}
        use Fixpoint.Ast.Shared.PredSym
        use Fixpoint.Counter
        use Fixpoint.Counter.Counter

        pub def computeMapping(d: AugmentedProgram): Map[RamID, Int32] = region rc {
            let disjointSet = MutDisjointSets.empty(rc);
            let AugmentedProgram.Program(s, _, predTrack, _) = d;
            computeDisjointStmt(s, predTrack, disjointSet);
            let mutMap = MutMap.empty(rc);
            let counter = Counter.empty(rc);
            computeMappingStmt(s, predTrack, disjointSet, mutMap, counter);
            let _ = "";
            Map.empty()
        }

        // pub def computeDisjointSet(d: AugmentedProgram): Unit = region rc {
        //     let disjoint = MutDisjointSets.empty(rc);
        //     let AugmentedProgram.Program(s, _, predTrack, _) = d;
        //     computeDisjointStmt(s, predTrack, disjoint);
        //     // disjoint
        //     ()
        // }

        def computeDisjointStmt(s: RamStmt, predTrack: PredSymMapInternal, set: MutDisjointSets[RamID, r]): Unit \ r = match s {
            case RamStmt.Insert(rest) => computeDisjointOp(rest, predTrack, set)
            case RamStmt.Merge(_, _) => ()
            case RamStmt.Swap(_, _) => ()
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(x -> computeDisjointStmt(x, predTrack, set), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(x -> computeDisjointStmt(x, predTrack, set), stmts)
            case RamStmt.Until(bools, stmt) => computeDisjointStmt(stmt, predTrack, set); Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools)
            case RamStmt.Comment(_) => ()
        }

        def computeDisjointOp(s: RelOp, predTrack: PredSymMapInternal, set: MutDisjointSets[RamID, r]): Unit \ r = match s {
            case RelOp.Search(TupleVar.Named(id), RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), rest) =>
                Vector.forEach(i -> MutDisjointSets.union(RamID.TuplePos(id, i), RamID.RelPos(predSym, i), set), Vector.range(0, arity));
                unifyPredTypes(predSym, arity, predTrack, set);
                computeDisjointOp(rest, predTrack, set)
            case RelOp.SearchWithIndex(TupleVar.Named(id), RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), bools, rest) =>
                Vector.forEach(i -> MutDisjointSets.union(RamID.TuplePos(id, i), RamID.RelPos(predSym, i), set), Vector.range(0, arity));
                unifyPredTypes(predSym, arity, predTrack, set);
                Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools);
                computeDisjointOp(rest, predTrack, set)
            case RelOp.Functional(AugmentedRam.TupleVar.Named(outID), _, inputTerms, rest, RamID.ID(_)) => // equality on the input should be handled elsewhere.
                Vector.forEachWithIndex(i -> curTerm -> {
                    let termID = AugmentedRam.getTermRamId(curTerm);
                    MutDisjointSets.union(RamID.FunctionalOutID(outID, i), termID, set); // Possibly not needed as it should be covered by equality
                    computeDisjointTerm(curTerm, predTrack, set)
                    // match curTerm {
                    //     case RamTerm.RowLoad(varr, index, ramID) => MutDisjointSets.makeSet(ramID, set); MutDisjointSets.makeSet((varr, index), set)
                    //     case _ => ()
                    // }
                }, inputTerms);
                computeDisjointOp(rest, predTrack, set);
                ??? // I think it works, so this should be removed
            case RelOp.Project(terms, sym) =>
                let fullSym = PredTrack.idToFullPredID(toPredID(sym), predTrack);
                Vector.forEachWithIndex(i -> term ->{
                    computeDisjointTerm(term, predTrack, set);
                    let termID = AugmentedRam.getTermRamId(term);
                    MutDisjointSets.union(RamID.RelPos(fullSym, i), termID, set)
                }, terms)
            case RelOp.If(bools, rest) =>
                Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools);
                computeDisjointOp(rest, predTrack, set)
            case RelOp.Functional(AugmentedRam.TupleVar.Named(outID), _, inputTerms, rest, _) => bug!("Functional should have RamID")
        }

        def computeDisjointBool(s: BoolExp, predTrack: PredSymMapInternal, set: MutDisjointSets[RamID, r]): Unit \ r = match s {
            case BoolExp.IsEmpty(_) => ()
            case BoolExp.NotMemberOf(terms, sym) => ???
            case BoolExp.Eq(term1, term2) => ???
            case BoolExp.Leq(_, term1, term2) => ???
            case BoolExp.Guard0(_) => ???
            case BoolExp.Guard1(_, term1) => ???
            case BoolExp.Guard2(_, term1, term2) => ???
            case BoolExp.Guard3(_, term1, term2, term3) => ???
            case BoolExp.Guard4(_, term1, term2, term3, term4) => ???
            case BoolExp.Guard5(_, term1, term2, term3, term4, term5) => ???
        }

        def unifyPredTypes(predSym: Int64, arity: Int32, predTrack: PredSymMapInternal, set: MutDisjointSets[RamID, r]): Unit \ r =
            let fullSymbol = PredTrack.idToFullPredID(predSym, predTrack);
            let deltaSymbol = PredTrack.fullIDtoPredType(fullSymbol, PredTrack.PredType.Delta, predTrack);
            let newSymbol = PredTrack.fullIDtoPredType(fullSymbol, PredTrack.PredType.New, predTrack);
            Vector.forEach(i -> MutDisjointSets.union(RamID.RelPos(fullSymbol, i), RamID.RelPos(deltaSymbol, i), set), Vector.range(0, arity));
            Vector.forEach(i -> MutDisjointSets.union(RamID.RelPos(fullSymbol, i), RamID.RelPos(newSymbol, i), set), Vector.range(0, arity));
            ()

        def computeDisjointTerm(s: RamTerm, predTrack: PredSymMapInternal, set: MutDisjointSets[RamID, r]): Unit \ r = match s {
            case RamTerm.Lit(_, _) => ()
            case RamTerm.RowLoad(_, _, _, _) => ()
            case RamTerm.LoadLatVar(_, _, _) => ()
            case RamTerm.Meet(_, t1, t2, RamID.ID(id)) => 
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                let id1 = AugmentedRam.getTermRamId(t1);
                let id2 = AugmentedRam.getTermRamId(t2);
                MutDisjointSets.union(id1, RamID.InID(id, 0), set);
                MutDisjointSets.union(id2, RamID.InID(id, 1), set);
                MutDisjointSets.union(id1, id2, set)
            case RamTerm.App0(_, _) => ()
            case RamTerm.App1(_, t1, RamID.ID(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                let id1 = AugmentedRam.getTermRamId(t1);
                MutDisjointSets.union(id1, RamID.InID(id, 0), set)
            case RamTerm.App2(_, t1, t2, RamID.ID(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                let id1 = AugmentedRam.getTermRamId(t1);
                let id2 = AugmentedRam.getTermRamId(t2);
                MutDisjointSets.union(id1, RamID.InID(id, 0), set);
                MutDisjointSets.union(id2, RamID.InID(id, 1), set)
            case RamTerm.App3(_, t1, t2, t3, RamID.ID(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                computeDisjointTerm(t3, predTrack, set);
                let id1 = AugmentedRam.getTermRamId(t1);
                let id2 = AugmentedRam.getTermRamId(t2);
                let id3 = AugmentedRam.getTermRamId(t3);
                MutDisjointSets.union(id1, RamID.InID(id, 0), set);
                MutDisjointSets.union(id2, RamID.InID(id, 1), set);
                MutDisjointSets.union(id3, RamID.InID(id, 2), set)
            case RamTerm.App4(_, t1, t2, t3, t4, RamID.ID(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                computeDisjointTerm(t3, predTrack, set);
                computeDisjointTerm(t4, predTrack, set);
                let id1 = AugmentedRam.getTermRamId(t1);
                let id2 = AugmentedRam.getTermRamId(t2);
                let id3 = AugmentedRam.getTermRamId(t3);
                let id4 = AugmentedRam.getTermRamId(t4);
                MutDisjointSets.union(id1, RamID.InID(id, 0), set);
                MutDisjointSets.union(id2, RamID.InID(id, 1), set);
                MutDisjointSets.union(id3, RamID.InID(id, 2), set);
                MutDisjointSets.union(id4, RamID.InID(id, 3), set)
            case RamTerm.App5(_, t1, t2, t3, t4, t5, RamID.ID(id)) =>
                computeDisjointTerm(t1, predTrack, set);
                computeDisjointTerm(t2, predTrack, set);
                computeDisjointTerm(t3, predTrack, set);
                computeDisjointTerm(t4, predTrack, set);
                computeDisjointTerm(t5, predTrack, set);
                let id1 = AugmentedRam.getTermRamId(t1);
                let id2 = AugmentedRam.getTermRamId(t2);
                let id3 = AugmentedRam.getTermRamId(t3);
                let id4 = AugmentedRam.getTermRamId(t4);
                let id5 = AugmentedRam.getTermRamId(t5);
                MutDisjointSets.union(id1, RamID.InID(id, 0), set);
                MutDisjointSets.union(id2, RamID.InID(id, 1), set);
                MutDisjointSets.union(id3, RamID.InID(id, 2), set);
                MutDisjointSets.union(id4, RamID.InID(id, 3), set);
                MutDisjointSets.union(id5, RamID.InID(id, 4), set)
            case _ => bug!("Unreachable")
        }

        @Internal
        def computeMappingStmt(s: RamStmt, predTrack: PredSymMapInternal, set: MutDisjointSets[RamID, r1], map: MutMap[RamID, Int32, r2], counter: Counter[r3]): Unit \ {r1, r2, r3} = match s {
            case RamStmt.Insert(rest) => computeMappingOp(rest, predTrack, set, map, counter)
            case RamStmt.Merge(_, _) => ()
            case RamStmt.Swap(_, _) => ()
            case RamStmt.Purge(_) => ()
            case RamStmt.Seq(stmts) => Vector.forEach(x -> computeMappingStmt(x, predTrack, set, map, counter), stmts)
            case RamStmt.Par(stmts) => Vector.forEach(x -> computeMappingStmt(x, predTrack, set, map, counter), stmts)
            case RamStmt.Until(bools, stmt) => 
                computeMappingStmt(stmt, predTrack, set, map, counter); 
                /*TODO: FIX BOOL*/
                Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools)
            case RamStmt.Comment(_) => ()
        }


        def computeMappingOp(s: RelOp, predTrack: PredSymMapInternal, set: MutDisjointSets[RamID, r1], map: MutMap[RamID, Int32, r2], counter: Counter[r3]): Unit \ {r1, r2, r3} = 
        let recurse = x -> computeMappingOp(x, predTrack, set, map, counter);
        match s {
            case RelOp.Search(_, _, rest) => recurse(rest)
            case RelOp.SearchWithIndex(TupleVar.Named(id), RelSym.Symbol(PredSym.PredSym(_, predSym), arity, _), bools, rest) =>
                // Vector.forEach(i -> MutDisjointSets.union(RamID.TuplePos(id, i), RamID.RelPos(predSym, i), set), Vector.range(0, arity));

                // unifyPredTypes(predSym, arity, predTrack, set);
                // Vector.forEach(x -> computeDisjointBool(x, predTrack, set), bools);
                // computeDisjointOp(rest, predTrack, set)
                ???
            case RelOp.Functional(AugmentedRam.TupleVar.Named(outID), _, inputTerms, rest, RamID.ID(_)) => // equality on the input should be handled elsewhere.
                ???
                // Vector.forEachWithIndex(i -> curTerm -> {
                //     let termID = AugmentedRam.getTermRamId(curTerm);
                //     MutDisjointSets.union(RamID.FunctionalOutID(outID, i), termID, set); // Possibly not needed as it should be covered by equality
                //     computeDisjointTerm(curTerm, predTrack, set)
                //     // match curTerm {
                //     //     case RamTerm.RowLoad(varr, index, ramID) => MutDisjointSets.makeSet(ramID, set); MutDisjointSets.makeSet((varr, index), set)
                //     //     case _ => ()
                //     // }
                // }, inputTerms);
                // computeDisjointOp(rest, predTrack, set);
                // ??? // I think it works, so this should be removed
            case RelOp.Project(terms, sym) =>
                Vector.forEach(x -> computeMappingTerm(x, predTrack, set, map, counter), terms)
            case RelOp.If(bools, rest) =>
                recurse(rest);
                ???
            case RelOp.Functional(AugmentedRam.TupleVar.Named(outID), _, inputTerms, rest, _) => bug!("Functional should have RamID")
        }


        def computeMappingTerm(s: RamTerm, predTrack: PredSymMapInternal, set: MutDisjointSets[RamID, r1], map: MutMap[RamID, Int32, r2], counter: Counter[r3]): Unit \ {r1, r2, r3} = 
        let insert = x -> insertIndex(x, set, map, counter);
        let recurse = x -> computeMappingTerm(x, predTrack, set, map, counter);
        match s {
            case RamTerm.Lit(_, id) => insert(id)
            case RamTerm.RowLoad(_, _, _, id) => insert(id)
            case RamTerm.LoadLatVar(_, _, id) => insert(id)
            case RamTerm.Meet(_, t1, t2, RamID.ID(id)) =>
                recurse(t1);
                recurse(t2);
                insert(RamID.ID(id));
                insert(RamID.InID(id, 0));
                insert(RamID.InID(id, 1))
            case RamTerm.App0(_, id) => insert(id)
            case RamTerm.App1(_, t1, RamID.ID(id)) =>
                recurse(t1);
                insert(RamID.ID(id));
                insert(RamID.InID(id, 0))
                // MutDisjointSets.union(id1, RamID.InID(id, 0), set)
            case RamTerm.App2(_, t1, t2, RamID.ID(id)) =>
                recurse(t1);
                recurse(t2);
                insert(RamID.ID(id));
                insert(RamID.InID(id, 0));
                insert(RamID.InID(id, 1))
            case RamTerm.App3(_, t1, t2, t3, RamID.ID(id)) =>
                recurse(t1);
                recurse(t2);
                recurse(t3);
                insert(RamID.ID(id));
                insert(RamID.InID(id, 0));
                insert(RamID.InID(id, 1));
                insert(RamID.InID(id, 2))
            case RamTerm.App4(_, t1, t2, t3, t4, RamID.ID(id)) =>
                recurse(t1);
                recurse(t2);
                recurse(t3);
                recurse(t4);
                insert(RamID.ID(id));
                insert(RamID.InID(id, 0));
                insert(RamID.InID(id, 1));
                insert(RamID.InID(id, 2));
                insert(RamID.InID(id, 3))
            case RamTerm.App5(_, t1, t2, t3, t4, t5, RamID.ID(id)) =>
                recurse(t1);
                recurse(t2);
                recurse(t3);
                recurse(t4);
                recurse(t5);
                insert(RamID.ID(id));
                insert(RamID.InID(id, 0));
                insert(RamID.InID(id, 1));
                insert(RamID.InID(id, 2));
                insert(RamID.InID(id, 3));
                insert(RamID.InID(id, 4))
            case _ => bug!("Unreachable")
        }




        def insertIndex(id: RamID, disjoint: MutDisjointSets[RamID, r1], map: MutMap[RamID, Int32, r2], counter: Counter[r3]): Unit \ {r1, r2, r3} = 
            let repID = unwrap(MutDisjointSets.find(id, disjoint)); match MutMap.get(repID, map) {
            case Some(v) => MutMap.put(id, v, map)
            case None => 
                let newID = Counter.getNewID(counter);
                MutMap.put(id, newID, map);
                MutMap.put(repID, newID, map)
        }
        def unwrap(v: Option[a]): a = match v {
            case Some(x) => x
            case None => bug!("Primitive value somehow exceeded the size it should fit into")
        }
    }





    def unwrap(v: Option[a]): a = match v {
        case Some(x) => x
        case None => bug!("Primitive value somehow exceeded the size it should fit into")
    }
}