mod Fixpoint.Helpers {
    import java.lang.Object
    import java.util.Objects
    
    pub def ptrEqual(o1: v, o2: v): Bool \ r = 
        let obj1 = unchecked_cast(o1 as Object \ r);
        let obj2 = unchecked_cast(o2 as Object \ r);
        unchecked_cast(Objects.equals(obj1, obj2) as _ \ r)

    pub def unwrap(x: Option[a]): a = match x {
        case Some(v) => v
        case None => bug!("Attempted unwrapping None")
    }  
    
}

mod Array {
    import java.lang.System
    import java.lang.Object

    pub def copyInto(srcPos: { srcPos = Int32 }, dstPos: { dstPos = Int32 }, len: { len = Int32 }, src: { src = Array[a, r1] }, dst: { dst = Array[a, r2] }): Unit \ { r1, r2 } =
        let srcObj: Object = checked_cast(src#src);
        let dstObj: Object = checked_cast(dst#dst);
        unchecked_cast(System.arraycopy(srcObj, srcPos#srcPos, dstObj, dstPos#dstPos, len#len) as _ \ { r1, r2 })

    pub def insert(x: a, i: Int32, len: Int32, v: Array[a, r]): Unit \ r =
        copyInto(srcPos = i, dstPos = i + 1, len = len - i, src = v, dst = v);
        Array.put(x, i, v)

}

mod MutList {

    pub def rawGet(i: Int32, list: MutList[v, r]): v \ r = Array.get(i, list->values)    

}