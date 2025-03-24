mod Fixpoint.Phase.IndexSelection {
    use AutomaticIndexSelection.{minIndex}
    use Fixpoint.Ast.Ram.{RamStmt, RamProgram, RelOp, BoolExp, RelSym, RamTerm, toId, Search};

    pub def indexProgram(program: RamProgram): RamProgram = match program {
        case RamProgram.Program(stmt, facts, meta, _) => 
            let index = Map.map(minIndex, indexStmt(stmt));
            RamProgram.Program(stmt, facts, meta, index)
    }

    def indexStmt(stmt: RamStmt): Map[Int64, List[Search]] = match stmt {
        case RamStmt.Seq(xs) => Vector.foldMap(x -> indexStmt(x), xs)
        case RamStmt.Insert(op) => indexOp(op)
        case _ => Map.empty()
    }

    def indexOp(op: RelOp): Map[Int64, List[Search]] = match op {
        case RelOp.Search(tupleVar, relSym, rest) => indexOp(rest)
        case RelOp.SearchWithIndex(tupleVar, relSym, boolExps, _, rest) =>
            let prefix = Vector.foldLeft(acc -> exp -> match exp {
                case BoolExp.Eq(t1, t2) => match t1 {
                    case RamTerm.RowLoad(_, i) => i :: acc
                    case _ => ???
                }
                case _ => acc
            }, List.empty(), boolExps);
            let search = List.toVector(List.reverse(prefix));
            let id = toId(relSym);
            let map = indexOp(rest);
            Map.insert(id, search :: Map.getWithDefault(id, List.empty(), map), map)
        case RelOp.If(_, rest) => indexOp(rest)
        case RelOp.Functional(_, _, _, rest) => indexOp(rest)
        case RelOp.Project(_, _) => Map.empty() 
    }

    mod AutomaticIndexSelection {
        //
        // This is based on the paper "Automatic Index Selection for Large-Scale Datalog
        // Computation" by Pavle Subotić, Herbert Jordan, Lijun Chang, Alan Fekete,
        // Bernhard Scholz (https://www.vldb.org/pvldb/vol12/p141-subotic.pdf)
        //
        use Fixpoint.Ast.Ram.{Search}
        type alias Vertex = Int32
        type alias Edge = (Vertex, Vertex)
        // Matching is a `Map` here so we can call `rangeQueryWith`
        type alias Matching = Map[Edge, Unit]
        type alias AdjacencyList = MultiMap[Vertex, Vertex]

        ///
        /// Find the maximum matching in the bipartite graph `(us, vs, edges)`.
        ///
        def maximumMatching(us: List[Vertex], vs: List[Vertex], adjList: AdjacencyList): Matching = region rc {
            let matching = Array.empty(rc, List.length(vs));
            let matchingRev = Array.empty(rc, List.length(us));
            Array.transform(_ -> -1, matching);
            def getMatching(u: Vertex, seen: Array[Bool, rc]): Bool \ rc = {
                let cond = v -> if (not Array.get(v, seen)) {
                    Array.put(true, v, seen);
                    if (Array.get(v, matching) < 0 or getMatching(Array.get(v, matching), seen)) {
                        Array.put(u, v, matching);
                        Array.put(v, u, matchingRev);
                        true
                    } else false
                } else false;
                Set.exists(cond, MultiMap.get(u, adjList))
            };
            List.filter(u -> getMatching(u, Array.empty(rc, List.length(us))), us) |>
            List.foldLeft(acc -> u -> Map.insert((u, Array.get(u, matchingRev)), (), acc), Map.empty())
        }

        ///
        /// Find the maximal path starting from the vertex `from_` in `matching`.
        ///
        def maximalPath(from_: Vertex, matching: Matching): List[Edge] = region rc {
            let allPaths = MutMap.empty(rc);
            def f(u: Vertex): Unit \ rc = match MutMap.get(u, allPaths) {
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
                case _ => ()
            };
            f(from_);
            match MutMap.get(from_, allPaths) {
                case Some(x) => x
                case None => List.empty()
            }
        }

        ///
        /// Create a graph from the list of searches `searches`.
        ///
        def graphFromSearches(searches: List[Search]): (List[Vertex], AdjacencyList) =
            // The vertices are are simply the indices of the searches in the list
            let vertices = List.range(0, List.length(searches));
            let sets = List.map(s -> Vector.toSet(s), searches);
            let zipped = List.zip(vertices, sets);
            let edgeList = List.foldMap(match (v1, s1) -> {
                List.filterMap(match (v2, s2) -> {
                    if (Set.isProperSubsetOf(s1, s2))
                        Some((v1, v2))
                    else None
                }, zipped)
            }, zipped);
            let adjList = List.foldLeft(a -> e -> {
                let (u, v) = e;
                MultiMap.insert(u, v, a)
            }, MultiMap.empty(), edgeList);
            (vertices, adjList)

        ///
        /// Find the minimum chain cover of `searches`.
        ///
        def minChainCover(searches: List[Search]): List[List[Search]] = 
            let (vertices, adjList) = graphFromSearches(searches);
            let searchesVec = List.toVector(searches);
            let matching = maximumMatching(vertices, vertices, adjList);
            let toSearch = i -> Vector.get(i, searchesVec);
            List.filter(v -> not Map.exists(edge -> _ -> snd(edge) == v, matching), vertices) |>
            List.foldLeft(acc -> u1 -> {
                let chain = toSearch(u1) :: List.map(e -> toSearch(snd(e)), maximalPath(u1, matching));
                chain :: acc
            }, List.empty())

        ///
        /// Find the minimum set of indexes that covers `searches`.
        ///
        pub def minIndex(searches: List[Search]): List[Search] = 
            minChainCover(searches) |> 
            List.map(chain -> List.zip(chain, Vector.empty() :: chain)) |>
            List.map(List.map(match (s1, s2) -> Vector.filter(x -> not Vector.memberOf(x, s2), s1))) |>
            List.map(chain -> List.fold(chain))

        pub def main(): Unit \ IO = 
            let u0: Search = Vector#{1,2};
            let u1: Search = Vector#{1,2,3};
            let u2: Search = Vector#{1,3};
            let u3: Search = Vector#{2};
            let indexes = minIndex(u0::u1::u2::u3::Nil);
            println(indexes)

    }

}