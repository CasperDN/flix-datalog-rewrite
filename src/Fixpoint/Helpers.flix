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

    pub def dprint(x: a): Unit \ r with ToString[a] = unchecked_cast(println(x) as _ \ r)

    /// Perform a binary search and return the index of `key` in `arr` if it exists.
    /// Otherwise, return (-insertionPoint - 1). See Java binary search documentation for arrays.
    pub def binarySearch(key: v, length: Int32, arr: Array[v, r]): Int32 \ r with Order[v] = 
        if (length == 0)
            -1
        else
            def f(l: Int32, r: Int32): Int32 \ r = {
                if (l <= r - 1) {
                    let m = (l + r) / 2;
                    match Array.get(m, arr) <=> key {
                        case Comparison.LessThan => f(m + 1, r)
                        case Comparison.GreaterThan => f(l, m)
                        case Comparison.EqualTo => m
                    }
                } else -l-1
            };
            f(0, length)

    pub def toInsertionPoint(i: Int32): Int32 = -i-1
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