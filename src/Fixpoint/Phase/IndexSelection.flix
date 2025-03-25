mod Fixpoint.Phase.IndexSelection {
    use AutomaticIndexSelection.{minIndex}
    use Fixpoint.Ast.Ram.{RamStmt, RamProgram, RelOp, BoolExp, RelSym, RamTerm, toId, Search, IndexInformation};
    type alias Indexes[r: Eff] = MutMap[Int64, List[Search], r]

    def _testtt(tupleVar: Int32, position: Int32, data: Map[k, Vector[RamTerm]]): Vector[RamTerm] = 
        ???

    pub def indexProgram(program: RamProgram): RamProgram = match program {
        case RamProgram.Program(stmt, facts, meta, _) => 
            let (indexes, newStmt) = region rc {
                let indexes = MutMap.empty(rc);
                let newStmt = collectSearchesStmt(stmt, indexes, rc);
                let newIndexes = 
                    MutMap.map(rc, minIndex, indexes) |>
                    MutMap.toMap |> 
                    Map.map(List.toVector);
                (newIndexes, newStmt)
            };
            RamProgram.Program(indexStmt(newStmt, indexes), facts, meta, indexes)
    }

    def indexStmt(stmt: RamStmt, indexInformation: IndexInformation): RamStmt = match stmt {
        case RamStmt.Seq(xs) => RamStmt.Seq(Vector.map(x -> indexStmt(x, indexInformation), xs))
        case RamStmt.Insert(op) => RamStmt.Insert(indexOp(op, indexInformation))
        case RamStmt.Merge(_, _) => stmt
        case RamStmt.Swap(_, _) => stmt
        case RamStmt.Purge(_) => stmt
        case RamStmt.Par(xs) => RamStmt.Par(Vector.map(x -> indexStmt(x, indexInformation), xs))
        case RamStmt.Until(boolExps, body) => RamStmt.Until(boolExps, indexStmt(body, indexInformation))
        case RamStmt.Comment(_) => stmt 
    }

    def indexOp(op: RelOp, indexInformation: IndexInformation): RelOp = match op {
        case RelOp.Search(tupleVar, relSym, body) => RelOp.Search(tupleVar, relSym, indexOp(body, indexInformation))
        case RelOp.SearchWithIndex(tupleVar, relSym, boolExps, _, body) =>
            let search = 
                Vector.foldLeft(acc -> exp -> match exp {
                    case BoolExp.Eq(RamTerm.RowLoad(_, i), _) => i :: acc
                    case BoolExp.Eq(_, RamTerm.RowLoad(_, i)) => i :: acc
                    case _ => bug!("In IndexSelection.indexOp: Found non-equality BoolExp in indexOp!")
                }, List.empty(), boolExps) |> List.toVector;
            let index = match Map.get(toId(relSym), indexInformation) {
                case Some(indexes) => 
                    match Vector.findIndexOf(index ->
                        Vector.slice(start = 0, end = Vector.length(search), index) |> 
                        Vector.forAll(x -> Vector.memberOf(x, search))
                    , indexes) {
                        case Some(v) => v
                        case None => 
                            bug!("In IndexSelection.indexOp: Could not find an index for search ${search} for relation ${relSym}")
                    }
                case None => 
                    bug!("In IndexSelection.indexOp: ${relSym} has no indexes!")
            };
            RelOp.SearchWithIndex(tupleVar, relSym, boolExps, index, body)
        case RelOp.If(boolExps, body) => RelOp.If(boolExps, indexOp(body, indexInformation))
        case RelOp.Functional(tupleVar, func, terms, body) => 
            RelOp.Functional(tupleVar, func, terms, indexOp(body, indexInformation))
        case RelOp.Project(_, _) => op
    }

    def collectSearchesStmt(stmt: RamStmt, indexes: Indexes[r], rc: Region[r]): RamStmt \ r = match stmt {
        case RamStmt.Seq(xs) => RamStmt.Seq(Vector.map(x -> collectSearchesStmt(x, indexes, rc), xs))
        case RamStmt.Insert(op) => RamStmt.Insert(collectSearchesOp(op, indexes, rc))
        case RamStmt.Merge(_, _) => stmt
        case RamStmt.Swap(_, _) => stmt
        case RamStmt.Purge(_) => stmt
        case RamStmt.Par(xs) => RamStmt.Par(Vector.map(x -> collectSearchesStmt(x, indexes, rc), xs))
        case RamStmt.Until(boolExps, body) => RamStmt.Until(boolExps, collectSearchesStmt(body, indexes, rc))
        case RamStmt.Comment(_) => stmt 
    }

    def collectSearchesOp(op: RelOp, indexes: Indexes[r], rc: Region[r]): RelOp \ r = match op {
        case RelOp.Search(tupleVar, relSym, body) => 
            RelOp.Search(tupleVar, relSym, collectSearchesOp(body, indexes, rc))
        case RelOp.SearchWithIndex(tupleVar, relSym, boolExps, _, body) =>
            let otherBoolExpList = MutList.empty(rc);
            let equalExpList = MutList.empty(rc);
            let search = 
                Vector.foldLeft(acc -> exp -> match exp {
                    case BoolExp.Eq(RamTerm.RowLoad(_, i), _) => 
                        MutList.push(exp, equalExpList);
                        i :: acc
                    case BoolExp.Eq(_, RamTerm.RowLoad(_, i)) => 
                        MutList.push(exp, equalExpList);
                        i :: acc
                    case _ => 
                        MutList.push(exp, otherBoolExpList);
                        acc
                }, List.empty(), boolExps) |> List.reverse |> List.toVector;
            let id = toId(relSym);
            let newBody = collectSearchesOp(body, indexes, rc);
            let searchList = MutMap.getWithDefault(id, List.empty(), indexes);
            MutMap.put(id, search :: searchList, indexes);
            let otherBoolExps = MutList.toVector(otherBoolExpList);
            let nestedBody = 
                if (Vector.length(otherBoolExps) == 0) newBody 
                else RelOp.If(otherBoolExps, newBody);
            let equalExps = MutList.toVector(equalExpList);
            if (Vector.length(equalExps) == 0)
                RelOp.Search(tupleVar, relSym, nestedBody)
            else
                RelOp.SearchWithIndex(tupleVar, relSym, equalExps, -1, nestedBody)
        case RelOp.If(boolExps, body) => RelOp.If(boolExps, collectSearchesOp(body, indexes, rc))
        case RelOp.Functional(tupleVar, func, terms, body) => 
            RelOp.Functional(tupleVar, func, terms, collectSearchesOp(body, indexes, rc))
        case RelOp.Project(_, _) => op
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
            let zipped = searches |> List.map(s -> Vector.toSet(s)) |> List.zip(vertices); 
            let adjList = List.foldMap(match (u, s) -> {
                    List.filter(p -> Set.isProperSubsetOf(s, snd(p)), zipped) |>
                    List.map(p -> (u, fst(p)))
                }, zipped) |> 
                List.foldLeft(a -> p -> {
                    let (u, v) = p;
                    MultiMap.insert(u, v, a)
                }, MultiMap.empty());
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
            List.map(List.fold)

        pub def main(): Unit \ IO = 
            let u0: Search = Vector#{2,1};
            let u1: Search = Vector#{1,2,3};
            let u2: Search = Vector#{1,3};
            let u3: Search = Vector#{2,3};
            let indexes = minIndex(u0::u1::u2::u3::Nil);
            println(indexes)

    }

}