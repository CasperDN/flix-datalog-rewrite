mod Fixpoint.Helpers {
    import java.lang.Object
    import java.util.Objects
}
mod Array {
    import java.lang.System
    import java.lang.Object

    pub def copyInto(srcPos: { srcPos = Int32 }, dstPos: { dstPos = Int32 }, len: { len = Int32 }, src: { src = Array[a, r1] }, dst: Array[a, r2]): Unit \ { r1, r2 } =
        let srcObj: Object = checked_cast(src#src);
        let dstObj: Object = checked_cast(dst);
        unchecked_cast(System.arraycopy(srcObj, srcPos#srcPos, dstObj, dstPos#dstPos, len#len) as _ \ { r1, r2 })

    pub def insert(x: a, i: Int32, len: Int32, v: Array[a, r]): Unit \ r =
        if (len == i)
            Array.put(x, i, v)
        else 
            copyInto(srcPos = i, dstPos = i + 1, len = len - i, src = v, v);
            Array.put(x, i, v)

}

mod MutList {

    pub def rawGet(i: Int32, list: MutList[v, r]): v \ r = Array.get(i, list->values)    

}