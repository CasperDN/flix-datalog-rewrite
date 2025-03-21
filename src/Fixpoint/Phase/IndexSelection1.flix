mod Fixpoint.IndexSelection1 {
    type alias Search = Vector[Int32]
    type alias Vertex = Int32
    type alias Edge = (Vertex, Vertex)
    // Matching is a `Map` here so we can call `rangeQueryWith`
    type alias Matching = Map[Edge, Unit]

    def maximumMatching(us: List[Vertex], vs: List[Vertex], edges: List[Edge]): Matching = region rc {
        let matching = Array.empty(rc, List.length(vs));
        Array.transform(_ -> -1, matching);
        def getMatching(u: Vertex, seen: Array[Bool, rc], currentEdges: List[Edge]): Bool \ rc = match currentEdges {
            case (u0, v) :: rest => 
                if (u0 == u and not Array.get(v, seen)) {
                    Array.put(true, v, seen);
                    if (Array.get(v, matching) < 0 or getMatching(Array.get(v, matching), seen, edges)) {
                        Array.put(u, v, matching);
                        true
                    } else getMatching(u, seen, rest)
                } else getMatching(u, seen, rest)        
            case _ => false
        };
        let matchedVertices = List.filter(u -> getMatching(u, Array.empty(rc, List.length(us)), edges), us);
        List.foldLeft(acc -> u -> {
            let v = match Array.findIndexOf(u0 -> u0 == u, matching) {
                case Some(i) => i
                case None => bug!("Something went wrong")
            };
            Map.insert((u, v), (), acc)
        }, Map.empty(), matchedVertices)
    }

    ///
    /// Find the maximal path starting from the vertex `from_` in `matching`
    ///
    def maximalPath(from_: Vertex, matching: Matching): List[Edge] = region rc {
        let allPaths = MutMap.empty(rc);
        def f(u: Vertex): Unit \ rc = match MutMap.get(u, allPaths) {
            case Some(_) => ()
            case None => Map.rangeQueryWith(
                edge -> fst(edge) <=> u, 
                edge -> _ -> {
                    let (u0, v0) = edge;
                    f(v0); // Compute the longest path of v0 and store in allPaths
                    let largest = l1 -> l2 -> if (List.length(l1) <= List.length(l2)) l2 else l1;
                    MutMap.putWith(
                        largest, u0, 
                        edge :: Option.getWithDefault(List.empty(), MutMap.get(v0, allPaths)), 
                        allPaths)
                }, matching)
        };
        f(from_);
        match MutMap.get(from_, allPaths) {
            case Some(x) => x
            case None => List.empty()
        }
    }

    def bipartiteGraphFromSearches(searches: List[Search]): (List[Vertex], List[Edge]) =
        // The vertices are are simply the indices of the searches in the list
        let vertices = List.range(0, List.length(searches));
        let sets = List.map(s -> Vector.toSet(s), searches);
        let zipped = List.zip(vertices, sets);
        let edges = List.foldMap(match (v1, s1) -> {
            List.filterMap(match (v2, s2) -> {
                if (Set.isProperSubsetOf(s1, s2))
                    Some((v1, v2))
                else None
            }, zipped)
        }, zipped);
        (vertices, edges)

    def minChainCover(searches: List[Search]): List[List[Search]] \ IO = 
        let (vertices, edges) = bipartiteGraphFromSearches(searches);
        let map = List.toMap(List.zip(vertices, searches)); // To map back to searches
        let matching = maximumMatching(vertices, vertices, edges);
        let cond = v -> not Map.exists(edge -> _ -> snd(edge) == v, matching);
        let valid = List.filter(cond, vertices);
        let toSearch = i -> match Map.get(i, map) {
            case Some(v) => v
            case None => ???
        };
        List.foldLeft(acc -> u1 -> {
            let maxPath = maximalPath(u1, matching);
            match maxPath {
                case x :: xs => (toSearch(fst(x)) :: List.map(e -> toSearch(snd(e)) , maxPath)) :: acc
                case Nil => (toSearch(u1) :: Nil) :: acc
            }
        }, List.empty(), valid)

    pub def main(): Unit \ IO = 
        let u0: Search = Vector#{1};
        let u1: Search = Vector#{1,2};
        let u2: Search = Vector#{1,3};
        let u3: Search = Vector#{1,2,3};
        let chains = minChainCover(u0::u1::u2::u3::Nil);
        println(chains)
}