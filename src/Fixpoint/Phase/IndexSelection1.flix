// mod Fixpoint.IndexSelection1 {
//     // (Maybe?) TODO: Encode searches as vertices and run algorithm on these
//     // and map them back to searches afterwards
//     type alias Search = Vector[Int32]
//     type alias Vertex = Search
//     type alias Edge = (Vertex, Vertex)
//     type alias Matching = Map[Edge, Unit]

//     def maximumMatching(): Matching = ???

//     def maximalPath(startVertex: Vertex, matching: Matching): List[Edge] = region rc {
//         let allPaths = MutMap.empty(rc);
//         def f(u: Vertex): Unit \ rc = match MutMap.get(u, allPaths) {
//             case Some(_) => ()
//             case None => Map.rangeQueryWith(
//                 edge -> fst(edge) <=> u, 
//                 edge -> _ -> {
//                     let (u0, v0) = edge;
//                     f(v0); // Compute the longest path of v0 and store in allPaths
//                     let largest = l1 -> l2 -> if (List.length(l1) <= List.length(l2)) l2 else l1;
//                     MutMap.putWith(
//                         largest, u0, 
//                         edge :: Option.getWithDefault(List.empty(), MutMap.get(v0, allPaths)), 
//                         allPaths)
//                 }, matching)
//         };
//         f(startVertex);
//         match MutMap.get(startVertex, allPaths) {
//             case Some(x) => x
//             case None => List.empty()
//         }
//     }

//     def _minChainCover(searches: List[Search]): List[Search] =
//         let edges = List.foldMap(s -> List.map(???, searches), searches);
//         let matching = maximumMatching(searches, searches, edges);
//         let cond = v -> not Map.exists(edge -> _ -> snd(edge) == v, matching);
//         let validSearches = List.filter(cond, searches);
//         List.foldLeft(acc -> s -> {
//             match maximalPath(s, matching) {
//                 case x :: xs => x :: List.map(e -> snd(e) , xs) :: acc
//                 case Nil => acc
//             }
//         }, List.empty(), validSearches)

//     pub def main(): Unit \ IO = 
//         let u1: Search = Vector#{1};
//         let u2: Search = Vector#{2};
//         let u3: Search = Vector#{3};
//         let u4: Search = Vector#{4};
//         let u5: Search = Vector#{5};
//         let u6: Search = Vector#{6};

//         let edges = (u1, u2) :: (u2, u3) :: (u1, u3) :: (u2, u4) :: (u5, u6) :: (u3, u5) :: Nil;
//         println(maximalPath(u1, List.foldLeft(a -> x -> Map.insert(x, (), a), Map.empty(), edges)))
// }