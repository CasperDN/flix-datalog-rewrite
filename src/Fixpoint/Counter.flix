mod Fixpoint.Counter {
    pub type alias Counter[r: Eff] = Ref[Int32, r]
    pub def empty(rc: Region[r]): Counter[r] \ r = Ref.fresh(rc, 0)

    pub def getNewID(c: Counter[r]): Int32 \ r =
        let newID = Ref.get(c);
        Ref.put(newID + 1, c);
        newID

    pub def resetTo(i: Int32, c: Counter[r]): Unit \ r =
        Ref.put(i, c)

    pub def getCurrentId(c: Counter[r]): Int32 \ r =
        Ref.get(c)

    // pub def getIncrementBy(c: Counter[r], i: Int32): Unit \ r =
    //     let newID = Ref.get(c);
    //     Ref.put(newID + i, c)

    pub def clone(c: Counter[r1], rc: Region[r2]): Counter[r2] \ {r1, r2} =
        Ref.fresh(rc, Ref.get(c))
}