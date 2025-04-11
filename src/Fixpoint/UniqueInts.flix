mod Fixpoint.UniqueInts {
    use Fixpoint.Counter
    use Fixpoint.Counter.Counter
    use Fixpoint.Helpers.unwrap
    
    pub type alias IndexState[k: Type, r: Region] = (MutMap[k, Int32, r], Counter[r])
    pub type alias ReverseState[k: Type] = Map[Int32, k]

    pub def empty(rc: Region[r]): IndexState[k, r] \ r = (MutMap.empty(rc), Counter.fresh(rc))

    pub def resetCounterTo(newState: Int32, state: IndexState[k, r]): Unit \ r = {
        let (_, counter) = state;
        Counter.resetTo(newState, counter)
    }

    pub def peek(state: IndexState[k, r]): Int32 \ r = {
        let (_, counter) = state;
        Counter.peek(counter)
    }


    pub def getIndex(val: k, state: IndexState[k, r]): Int32 \ r with Order[k] = 
        let (map, counter) = state;
        match MutMap.get(val, map) {
            case None =>
                let id = Counter.getNewID(counter);
                MutMap.put(val, id, map);
                id
            case Some(v) => v
        }

    pub def fromIndex(val: Int32, reverseState: ReverseState[k]): k = 
        unwrap(Map.get(val, reverseState))

    pub def reverse(state: IndexState[k, r]): ReverseState[k] \ r with Order[k] =
        let (map, _) = state;
        MutMap.foldLeftWithKey(acc -> k -> v -> Map.insert(v, k, acc), Map#{}, map)
}