mod Fixpoint.BTree {
    type alias Compare[v] = v -> v -> Comparison
   
    struct BLinkTree[v, r] {
        mut root: Node[v, r],
        order:    Int32,
        rc:       Region[r]
    }

    enum Node[v: Type, r: Eff] {
        case Internal(MutList[Node[v, r], r], MutList[v, r], NodeData[v, r])
        case Leaf(MutList[v, r], NodeData[v, r])
    }
    
    struct NodeData[v, r] {
        mut parent: Option[Ref[Node[v, r], r]],
        mut next:   Option[Ref[Node[v, r], r]]
    }


    mod Node {
        use Fixpoint.BTree.{NodeData, Node}
        pub def getData(node: Node[v, r]): NodeData[v, r]  = match node {
            case Node.Internal(_, _, data) => data
            case Node.Leaf(_, data)        => data
        }
        pub def getParent(node: Node[v, r]): Option[Ref[Node[v, r], r]] \ r               = NodeData.getParent(getData(node))
        pub def getNext(node: Node[v, r]): Option[Ref[Node[v, r], r]] \ r                 = NodeData.getNext(getData(node))
        pub def setParent(node: Node[v, r], parent: Option[Ref[Node[v, r], r]]): Unit \ r = NodeData.setParent(getData(node), parent)
        pub def setNext(node: Node[v, r], next: Option[Ref[Node[v, r], r]]): Unit \ r     = NodeData.setNext(getData(node), next)

    }

    mod NodeData {
        use Fixpoint.BTree.Node
        pub def getParent(data: NodeData[v, r]): Option[Ref[Node[v, r], r]] \ r               = data->parent
        pub def getNext(data: NodeData[v, r]): Option[Ref[Node[v, r], r]] \ r                 = data->next
        pub def setParent(data: NodeData[v, r], parent: Option[Ref[Node[v, r], r]]): Unit \ r = data->parent = parent
        pub def setNext(data: NodeData[v, r], next: Option[Ref[Node[v, r], r]]): Unit \ r     = data->next = next
    }

    mod BLinkTree {
        use Fixpoint.BTree.{NodeData, Node, Compare}

        pub def empty(rc: Region[r], order: Int32): BLinkTree[v, r] \ r = 
            let nodeData = new NodeData @ rc { 
                parent = Option.None, 
                next = Option.None
            };
            new BLinkTree @ rc { 
                root = Node.Leaf(MutList.empty(rc), nodeData), 
                order = order,
                rc = rc 
            }

        def unwrap(x: Option[a]): a = match x {
            case Some(v) => v
            case None => bug!("Attempted unwrapping None")
        }  

        // def findIndexOf(f: v -> Bool \ r1, list: MutList[v, r0]): Option[Int32] \ {r0, r1} = 
        //     def findInternal(index: Int32): Option[Int32] \ {r0, r1} = {
        //         if (index >= MutList.length(list)) 
        //             None
        //         else
        //             // Casting here is not 'right', but do not want possible Option overhead since the operation is done often.
        //             (if(unchecked_cast(f(MutList.get(index, list)) as _ \ {r0, r1}))
        //                 Some(index)
        //             else findInternal(index+1))
        //     };
        //     findInternal(0)

        pub def main2(): Unit \ {IO} = region rc {
            let list = MutList.empty(rc);
            MutList.push(2, list);
            MutList.push(4, list);
            MutList.push(6, list);
            MutList.push(8, list);
            let compare: Int32 -> Int32 -> Comparison = x -> y -> {
                if (x < y) Comparison.LessThan
                else if (x > y) Comparison.GreaterThan
                else Comparison.EqualTo
            };
            println(unchecked_cast(binarySearch(9, list, compare) as _ \ IO))
        }

        def binarySearch(keys: v, list: MutList[v, r], compare: Compare[v]): Int32 \ r = 
            if (MutList.isEmpty(list)) 
                0
            else
                def f(l: Int32, r: Int32): Int32 \ r = {
                    if (l <= r) {
                        let m = (l + r) / 2;
                        let cur = unwrap(MutList.nth(m, list));
                        if (compare(cur, keys) == Comparison.LessThan) f(m + 1, r)
                        else if (compare(cur, keys) == Comparison.GreaterThan) f(l, m - 1)
                        else m
                    } else if (l != 0) r + 1 else 0
                }; 
                f(0, MutList.length(list) - 1)

        def traverse(node: Node[v, r], val: v, compare: Compare[v]): Node[v, r] \ r = match node {
            case Node.Internal(children, keys, _) =>
                let index = binarySearch(val, keys, compare);
                let childToVisit = MutList.nth(index, children);
                // let findGreaterChild: Node[v, r] -> Bool \ r = child -> {
                //     let keys = Node.getKeys(child);
                //     compare(val, keys) == Comparison.LessThan
                // };
                // let childToVisit = match findIndexOf(findGreaterChild, children) {
                //     case Some(index) =>  MutList.nth(index, children)                       
                //     case None => MutList.last(children)
                // };
                traverse(unwrap(childToVisit), val, compare)
            case _ => node
        }

        def innerInsert(node: Node[v, r], val: v, compare: Compare[v], order: Int32, rc: Region[r]): Unit \ r = match traverse(node, val, compare) {
            case Node.Leaf(values, _) => 
                let length = MutList.length(values);
                if (length + 1 >= order) 
                    splitLeaf(node, val, compare, order, rc)
                else 
                    let index = binarySearch(val, values, compare);
                    MutList.insert(val, index, values)
            case _ => unreachable!()
        }

        pub def insert(tree: BLinkTree[v, r], val: v, compare: Compare[v]): Unit \ r = 
            innerInsert(tree->root, val, compare, tree->order, tree->rc)

        def splitLeaf(leftLeaf: Node[v, r], val: v, compare: Compare[v], order: Int32, rc: Region[r]): Unit \ r = match leftLeaf {
            case Node.Leaf(values, leftData) => 
                // Split the values into two halves
                let arr = MutList.toArray(rc, values);
                // TODO: Double-check that we dont lose the middle value here
                let rightArr = Array.copyOfRange(rc, MutList.length(values) / 2, MutList.length(values), arr);
                MutList.truncate(MutList.length(values) / 2, values); 
                let rightList = Array.toMutList(rc, rightArr);
                // By default we insert the new value into the right half
                MutList.insert(val, binarySearch(val, rightList, compare), rightList);
                // Get the parent if it exists or create a new one
                let parent = match NodeData.getParent(leftData) {
                    case None => 
                        let nodeData = new NodeData @ rc {
                            parent = Option.None,
                            next = Option.None
                        };
                        let children = MutList.empty(rc);
                        let keys = MutList.empty(rc);
                        // We only add the left leaf here since if it already existed
                        // it would contain the the left leaf
                        MutList.push(leftLeaf, children); 
                        MutList.push(unwrap(MutList.head(values)), keys);
                        let parent = Node.Internal(children, keys, nodeData);
                        Ref.fresh(rc, parent)
                    case Some(parent) => parent
                };

                // Create a new leaf to store the right half
                let rightData = new NodeData @ rc {
                    parent = Option.Some(parent),
                    next = NodeData.getNext(leftData)
                };
                let rightLeaf = Node.Leaf(rightList, rightData);
                // Update the old leaf's fields
                NodeData.setParent(leftData, Option.Some(parent));
                NodeData.setNext(leftData, Option.Some(Ref.fresh(rc, rightLeaf)));
                // Push key up to parent
                let newKey = unwrap(MutList.head(rightList));
                splitInternal(parent, newKey, leftLeaf, rightLeaf, compare, order, rc)
                
            case _ => unreachable!()
        }

        def splitInternal(node: Ref[Node[v, r], r], 
                          newKey: v, 
                          leftChild: Node[v, r],
                          rightChild: Node[v, r],
                          compare: Compare[v], 
                          order: Int32, 
                          rc: Region[r]): Unit \ r = match Ref.get(node) {
            case Node.Internal(children, keys, data) => 
                let length = MutList.length(children);
                if (length + 1 >= order) 
                    ???
                else 
                    let index = ???;
                    ???
                    // MutList.insert(newKey, keys, ?v)
            case _ => unreachable!()
        }
    }

}