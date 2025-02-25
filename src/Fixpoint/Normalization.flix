use Fixpoint.Boxed.BoxedObject
///
/// The purpose of this file is to map boxed constants to Int64 
/// since the indices on relations work on Int64 due to the lower
/// complexity of working with integers
///
mod Fixpoint.Normalization {
    use Fixpoint.Boxed
    use Fixpoint.Boxable
    use Fixpoint.Boxed.{BoxedBool, BoxedChar, BoxedInt8, BoxedInt16, BoxedInt32, BoxedInt64, BoxedFloat32, BoxedFloat64, BoxedObject}
    use Fixpoint.Normalization.ObjectMarshallingInfo
    use Fixpoint.Ast.Ram.RelSym
    import java.lang.{Float, Double, Object, Character}

    // Do not want to implement an ArrayList, but would be nice with a Flix ArrayList wrapper

    // It would be nice if MutMap could take a comparison
    pub type alias ObjectMarshallingInfo[r: Eff] = (MutList[Object, r], MutMap[Boxed, Int64, r])

    pub enum RealType {
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

    def deMarshalObject(index: Int64, info: ObjectMarshallingInfo[r]): Object \ r = {
        unwrap(MutList.nth(unwrap(Int64.tryToInt32(index)), fst(info)))
        // unchecked_cast(fst(info).get(unwrap(Int64.tryToInt32(index))) as _ \ {})
    }

    // We could Box the object and thus have a Boxed as input and be able to sort them?
    def marshallObject(box: Boxed, info: ObjectMarshallingInfo[r]): Int64 \ r = {
        let map = snd(info);
        // let cmp = (o1, o2) -> Order.compare(unchecked_cast(o1 as a), unchecked_cast(o2 as a));
        // let box = Boxed.BoxedObject(unchecked_cast(x as Object), cmp);
        let obj = match box {
            case BoxedObject(x, _) => x
            case _ => bug!("Marshalling non-object value")
        };
        // let max = 
        match MutMap.get(box, map) {
            case Some(id)   => id
            case None       => 
                let id = getNextIndex(info);
                MutList.insert(obj, id, fst(info));
                // let id_ = unchecked_cast({fst(info).add(id, unchecked_cast(x as Object)); id} as _ \ {});
                Int32.toInt64(id)
        }
        // let index = MutMap.getOrElsePut(box, getNextIndex(info), map);
        // ???
        // MutMap.get()
    }

    // TODO: Not thread safe. Apply locking (or use an AtomicInteger). Locking is needed for MutList anyway.
    def getNextIndex(info: ObjectMarshallingInfo[r]): Int32 \ r = {
        MutList.length(fst(info))
    }


    pub def normalizeBox(box: Boxed, info: ObjectMarshallingInfo[r]): Int64 \ r = match box {
        case BoxedBool(x)       => if (x) 1i64 else 0i64
        case BoxedChar(x)       => Int32.toInt64(Char.toBmpCodePoint(x)) // TODO: Confirm with Magnus
        case BoxedInt8(x)       => Int8.toInt64(x)
        case BoxedInt16(x)      => Int16.toInt64(x)
        case BoxedInt32(x)      => Int32.toInt64(x)
        case BoxedInt64(x)      => x
        case BoxedFloat32(x)    => Int32.toInt64(Float.floatToRawIntBits(Float32.valueOf(x).floatValue()))
        case BoxedFloat64(x)    => Double.doubleToRawLongBits(Float64.valueOf(x).doubleValue())
        case BoxedObject(_, _)  => marshallObject(box, info)
    }

    pub def normalizeReal(value: v, info: ObjectMarshallingInfo[r]): Int64 \ r with Order[v] = normalizeBox(Boxable.box(value), info)

    pub def getRealType(r: RelSym, index: Int32): RealType =
        ???
        // RealType.Bool
    

    // pub def normalizeReal(value: v, info: ObjectMarshallingInfo[r]): Int64 \ r with Order[v] = typematch value {
    //     case x: Bool    => if (x) 1i64 else 0i64
    //     case x: Char    => Int32.toInt64(Char.toBmpCodePoint(x)) // TODO: Confirm with Magnus
    //     case x: Int8    => Int8.toInt64(x)
    //     case x: Int16   => Int16.toInt64(x)
    //     case x: Int32   => Int32.toInt64(x)
    //     case x: Int64   => x
    //     case x: Float32 => Int32.toInt64(Float.floatToRawIntBits(Float32.valueOf(x).floatValue()))
    //     case x: Float64 => Double.doubleToRawLongBits(Float64.valueOf(x).doubleValue())
    //     case _: Object  => marshallObject(value, info)
    //     case _: _       => bug!("Cannot normalize value")
    // }

    pub def unNormalizeReal(v: Int64, wantedType: RealType, info: ObjectMarshallingInfo[r]): a \ r = match wantedType {
        case RealType.Bool      => unchecked_cast (not(v == 0i64) as a)
        case RealType.Char      => unchecked_cast(Array.get(0, Character.toChars(unwrap(Int64.tryToInt32(v)))) as a \ {})
        case RealType.Int8      => unchecked_cast(unwrap(Int64.tryToInt8(v)) as a)
        case RealType.Int16     => unchecked_cast(unwrap(Int64.tryToInt16(v)) as a)
        case RealType.Int32     => unchecked_cast(unwrap(Int64.tryToInt32(v)) as a)
        case RealType.Int64     => unchecked_cast(v as a)
        case RealType.Float32   => unchecked_cast(Float.intBitsToFloat(unwrap(Int64.tryToInt32(v))) as a)
        case RealType.Float64   => unchecked_cast(Float.intBitsToFloat(unwrap(Int64.tryToInt32(v))) as a)
        case RealType.Object    => unchecked_cast(deMarshalObject(v, info) as a)
    }
    
    
    // typematch (Proxy.Proxy: Proxy[a]) {
    //     case _: Proxy[Bool]     => unchecked_cast(if (v == 0i64) false else true as a)
    //     case _: Proxy[Char]     => unchecked_cast(Array.get(0, Character.toChars(unwrap(Int64.tryToInt32(v)))) as a \ {})
    //     case _: Proxy[Int8]     => unchecked_cast(unwrap(Int64.tryToInt8(v)) as a)
    //     case _: Proxy[Int16]    => unchecked_cast(unwrap(Int64.tryToInt16(v)) as a)
    //     case _: Proxy[Int32]    => unchecked_cast(unwrap(Int64.tryToInt32(v)) as a)
    //     case _: Proxy[Int64]    => unchecked_cast(v as a)
    //     case _: Proxy[Float32]  => unchecked_cast(Float.intBitsToFloat(unwrap(Int64.tryToInt32(v))) as a)
    //     case _: Proxy[Float64]  => unchecked_cast(Double.longBitsToDouble(v) as a)
    //     case _: Proxy[Object]   => unchecked_cast(deMarshalObject(v, info) as a)
    //     case _: _               => bug!("Cannot deNormalize value")
    // }

    def unwrap(v: Option[a]): a = match v {
        case Some(x) => x
        case None => bug!("Primitive value somehow exceeded the size it should fit into")
    }

}