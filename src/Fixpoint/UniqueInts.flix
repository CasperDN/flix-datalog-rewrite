mod Fixpoint.UniqueInts {
    use Fixpoint.Counter
    use Fixpoint.Counter.Counter
    
    pub type alias IndexState[k: Type, r: Region] = (MutMap[k, Int32, r], Counter[r])

    pub def empty(rc: Region[r]): IndexState[k, r] \ r = (MutMap.empty(rc), Counter.empty(rc))

    pub def getIndex(val: k, info: IndexState[k, r]): Int32 \ r with Order[k] = 
        let (map, counter) = info;
        match MutMap.get(val, map) {
            case None =>
                let id = Counter.getNewID(counter);
                MutMap.put(val, id, map);
                id
            case Some(v) => v
        }
}