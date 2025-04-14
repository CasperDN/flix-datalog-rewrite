mod Fixpoint.Counter {
    pub type alias Counter[r: Eff] = Ref[Int32, r]
    pub def fresh(rc: Region[r]): Counter[r] \ r = Ref.fresh(rc, 0)

    pub def getNewID(c: Counter[r]): Int32 \ r =
        let newID = Ref.get(c);
        Ref.put(newID + 1, c);
        newID

    pub def resetTo(i: Int32, c: Counter[r]): Unit \ r =
        Ref.put(i, c)

    pub def increment(c: Counter[r]): Unit \ r =
        Ref.put(Ref.get(c) + 1, c);
        ()

    pub def peek(c: Counter[r]): Int32 \ r =
        Ref.get(c)

    pub def clone(c: Counter[r1], rc: Region[r2]): Counter[r2] \ {r1, r2} =
        Ref.fresh(rc, Ref.get(c))

    pub def ++(c: Counter[r]): Int32 \ r = getNewID(c)

}