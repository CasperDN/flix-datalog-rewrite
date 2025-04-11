mod Fixpoint.PrecedenceGraph {
    pub type alias Vertex = Int32

    pub enum StronglyConnectedComponent {
        case SCC(Set[Vertex])
    }

    pub struct MutGraph[r] {
        vertices: MutSet[Vertex, r],
        adjList: MutMap[Vertex, List[Vertex], r]
    }

    mod MutGraph {
        use KeyNotFound.keyNotFound
        use Fixpoint.PrecedenceGraph.MutGraph.stronglyConnectedComponents
        use Fixpoint.Counter
        use Fixpoint.Counter.{Counter}
        use Fixpoint.PrecedenceGraph.Vertex
        use Fixpoint.PrecedenceGraph.StronglyConnectedComponent
        use Fixpoint.Helpers.unwrap

        pub enum Color with Eq {
            case White,
            case Gray,
            case Black
        }

        pub def addEdge(u: Vertex, v: Vertex, g: MutGraph[r]): Unit \ r = {
            MutSet.add(v, g->vertices);
            MutSet.add(u, g->vertices);
            let neighbors = MutMap.getWithDefault(u, List.empty(), g->adjList);
            if (List.memberOf(v, neighbors)) ()
            else MutMap.put(u, v :: neighbors, g->adjList)
        }
        
        pub def hasEdge(u: Vertex, v: Vertex, g: MutGraph[r]): Bool \ r = 
            g->adjList |> MutMap.getWithDefault(u, List.empty()) |> List.memberOf(v)
        
        pub def getVertices(g: MutGraph[r]): MutSet[Vertex, r] = g->vertices

        pub def getSize(g: MutGraph[r]): Int32 \ r = MutSet.size(g->vertices)

        pub def empty(rc: Region[r]): MutGraph[r] \ r = 
            new MutGraph @ rc {
                vertices = MutSet.empty(rc),
                adjList = MutMap.empty(rc)
            }

        pub def main199(): Unit \ IO = region rc {
            let g = empty(rc);
            addEdge(1, 2, g);
            println(toString(g))
        }

        pub def toString(g: MutGraph[r]): String \ r = 
            let edges = MutMap.joinWith(u -> v -> "\n  ${u} -> ${v}", ",", g->adjList);
            "MutGraph(${edges})"

        pub def computeSCCOrder(g: MutGraph[r]): List[StronglyConnectedComponent] \ r = region rc {
            let components = stronglyConnectedComponents(g);
            let contractedGraph = empty(rc);
            let componentMap: MutMap[Vertex, StronglyConnectedComponent, rc] = MutMap.empty(rc);
            let rootMap: MutMap[Vertex, Vertex, rc] = MutMap.empty(rc);
            components |> 
            List.forEachWithIndex(i -> match StronglyConnectedComponent.SCC(set) -> {
                set |> Set.forEach(partOfComp -> MutMap.put(partOfComp, i, rootMap));
                set |> Set.forEach(partOfComp -> 
                    MutMap.put(partOfComp, StronglyConnectedComponent.SCC(set), componentMap)
                )
            }); 
            
            g->adjList |> MutMap.forEach(u -> neighbors -> 
                neighbors |> List.forEach(v -> 
                contractedGraph |> 
                addEdge(
                    unwrap(MutMap.get(u, rootMap)), 
                    unwrap(MutMap.get(v, rootMap)))
                )
            );
            topologicalSort(contractedGraph) |> List.map(u -> unwrap(MutMap.get(u, componentMap)))
        }

        pub def topologicalSort(g: MutGraph[r]): List[Vertex] \ r = region rc {
            let sorted = MutList.empty(rc);
            let colors = Array.repeat(rc, getSize(g), Color.White);
            getVertices(g) |>
            MutSet.forEach(u -> {
                if (Array.get(u, colors) == Color.White) {
                    topologicalSortVisit(g, colors, sorted, u)
                } else ()
            });
            sorted |> MutList.toList 
        }

        def topologicalSortVisit(
            g: MutGraph[r1], 
            colors: Array[Color, r0], 
            sorted: MutList[Vertex, r0], 
            u: Vertex
        ): Unit \ r0 + r1 = {
            Array.put(Color.Gray, u, colors);
            getNeighbors(u, g) |>
            List.forEach(v -> {
                if (Array.get(v, colors) == Color.White) 
                    topologicalSortVisit(g, colors, sorted, v)
                else if (Array.get(v, colors) == Color.Gray)
                    bug!("In PrecedenceGraph.MutGraph.topologicalSortVisit: Cycle detected")
                else ()
            });
            Array.put(Color.Black, u, colors);
            MutList.push(u, sorted)
        }
        
        pub def stronglyConnectedComponents(g: MutGraph[r]): List[StronglyConnectedComponent] \ r = region rc {
            let n = getSize(g);
            let disc = Array.repeat(rc, n, -1);
            let low = Array.repeat(rc, n, -1);
            let onStack = Array.empty(rc, n);
            let stack = MutList.empty(rc);
            let components = MutList.empty(rc);

            let time = Counter.fresh(rc);
            getVertices(g) |> 
            MutSet.forEach(u ->
                if (Array.get(u, disc) == -1) {
                    stronglyConnectedComponentsVisit(
                        components, stack, disc, low, onStack, time, g, u
                    )
                } else ()
            );
            components |> MutList.toList
        }

        def getNeighbors(u: Vertex, g: MutGraph[r]): List[Vertex] \ r = 
            MutMap.getWithDefault(u, List.empty(), g->adjList) 

        def stronglyConnectedComponentsVisit(
            components: MutList[StronglyConnectedComponent, r0],
            stack: MutList[Vertex, r0],
            disc: Array[Int32, r0],
            low: Array[Int32, r0],
            onStack: Array[Bool, r0],
            time: Counter[r0],
            g: MutGraph[r1],
            u: Vertex
        ): Unit \ r0 + r1 = {
            Array.put(Counter.peek(time), u, disc);
            Array.put(Counter.peek(time), u, low);
            Counter.increment(time);
            Array.put(true, u, onStack);
            MutList.push(u, stack);

            getNeighbors(u, g) |>
            List.forEach(v -> {
                if (Array.get(v, disc) == -1) {
                    stronglyConnectedComponentsVisit(
                        components, stack, disc, low, onStack, time, g, v
                    );
                    let uLow = Array.get(u, low);
                    let vLow = Array.get(v, low);
                    Array.put(Int32.min(uLow, vLow), u, low)
                } else if (Array.get(v, onStack)) {
                    let uLow = Array.get(u, low);
                    let vLow = Array.get(v, low);
                    Array.put(Int32.min(uLow, vLow), u, low)
                } else ()
            });
            if (Array.get(u, low) == Array.get(u, disc)) {
                region rc {
                    let mutSet = MutSet.empty(rc);
                    def loop() = {
                        let w = match MutList.pop(stack) {
                            case Some(v) => v
                            case None => ???
                        };
                        Array.put(false, w, onStack);
                        MutSet.add(w, mutSet);
                        if (u != w) loop() 
                        else ()
                    };
                    loop();
                    let component = StronglyConnectedComponent.SCC(MutSet.toSet(mutSet));
                    MutList.push(component, components)
                }
            } else ()
        }
    }

}

