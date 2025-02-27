mod Fixpoint {
    type alias Compare[v] = v -> v -> Comparison

    def unwrap(x: Option[a]): a = match x {
        case Some(v) => v
        case None => bug!("Attempted unwrapping None")
    }  

    struct BLinkTree[v, r] {
        mut root: Node[v, r],
        order:    Int32,
        rc:       Region[r]
    }
    
    struct Node[v, r] {
        keys:       MutList[v, r], // Acts as keys for internal nodes and values for leaves
        children:   Option[MutList[Node[v, r], r]],
        mut parent: Option[Node[v, r]],
        mut next:   Option[Node[v, r]]
    }   
    
    
    mod MutList {
        use Fixpoint.{unwrap, Compare}
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
            println(unchecked_cast(binarySearch(4, list, compare, true) as _ \ IO))
        }    

        pub def sortedInsert(x: v, list: MutList[v, r], compare: Compare[v]): Unit \ r = 
            let index = binarySearch(x, list, compare, false);
            MutList.insert(x, index, list)


        pub def binarySearch(key: v, list: MutList[v, r], compare: Compare[v], traverse: Bool): Int32 \ r = 
            if (MutList.isEmpty(list)) 
                0
            else
                def f(l: Int32, r: Int32): Int32 \ r = {
                    if (l <= r) {
                        let m = (l + r) / 2;
                        let cur = unwrap(MutList.nth(m, list));
                        if (compare(cur, key) == Comparison.LessThan) f(m + 1, r)
                        else if (compare(cur, key) == Comparison.GreaterThan) f(l, m - 1)
                        else if (traverse) m + 1 else m
                    } else if (l != 0) r + 1 else 0
                }; 
                f(0, MutList.length(list) - 1)

    }

    mod Node {
        use Fixpoint.{Node, Compare, unwrap}
        use Fixpoint.MutList.{binarySearch, sortedInsert}
        pub def parent(node: Node[v, r]): Option[Node[v, r]] \ r = node->parent
        pub def next(node: Node[v, r]): Option[Node[v, r]] \ r = node->next
        pub def children(node: Node[v, r]): Option[MutList[Node[v, r], r]]  = node->children
        pub def keys(node: Node[v, r]): MutList[v, r] = node->keys

        // Traverse the tree until a leaf is reached
        pub def traverse(node: Node[v, r], val: v, compare: Compare[v]): Node[v, r] \ r = match node->children {
            case Some(children) =>
                let index = binarySearch(val, node->keys, compare, true);
                let childToVisit = match MutList.nth(index, children) {
                    case Some(child) => child
                    case None => unwrap(MutList.last(children))
                };
                traverse(childToVisit, val, compare)
            case None => node
        }

        // Insert a value into a leaf, potentially causing a split and returning a new root
        pub def insertIntoLeaf(node: Node[v, r], val: v, compare: Compare[v], order: Int32, rc: Region[r]): Option[Node[v,r]] \ r with ToString[v] = 
            let length = MutList.length(node->keys);
            if (length + 1 >= order) 
                splitLeaf(node, val, compare, order, rc)
            else {
                sortedInsert(val, node->keys, compare);
                None
            }

        // Split a leaf and push the middle key into the parent, potentially causing the parent to split and return a new root
        def splitLeaf(leftLeaf: Node[v, r], val: v, compare: Compare[v], order: Int32, rc: Region[r]): Option[Node[v, r]] \ r with ToString[v] = 
            let values = leftLeaf->keys;
            let arr = MutList.toArray(rc, values);
            // TODO: Double-check that we dont lose the middle value here
            let rightArr = Array.copyOfRange(rc, order / 2, MutList.length(values), arr);
            unchecked_cast(println("Before truncate: ${MutList.toVector(values)}") as _ \ r);
            MutList.truncate(order / 2, values); 
            let rightList = Array.toMutList(rc, rightArr);
            // Decide where to insert val
            if (compare(val, unwrap(MutList.last(values))) != Comparison.GreaterThan)
                    sortedInsert(val, values, compare)
                else 
                    sortedInsert(val, rightList, compare);
            unchecked_cast(println("leftList: ${MutList.toVector(values)}") as _ \ r);
            unchecked_cast(println("rightList: ${MutList.toVector(rightList)}") as _ \ r);
            // Create a new leaf to store the right half
            let rightLeaf = new Node @ rc {
                keys = rightList,
                children = None,
                parent = leftLeaf->parent,
                next = leftLeaf->next
            };
            // Update the old leaf's fields
            leftLeaf->next = Some(rightLeaf);
            // Push key up to parent
            let newKey = unwrap(MutList.head(rightList));
            pushKeyToParent(leftLeaf->parent, newKey, leftLeaf, rightLeaf, compare, order, rc)

        def splitInternal(node: Node[v, r], 
                          newKey: v, 
                          leftChild: Node[v, r],
                          rightChild: Node[v, r],
                          compare: Compare[v], 
                          order: Int32, 
                          rc: Region[r]): Option[Node[v, r]] \ r = ???


        def pushKeyToParent(parent: Option[Node[v, r]], 
                          newKey: v, 
                          leftChild: Node[v, r],
                          rightChild: Node[v, r],
                          compare: Compare[v], 
                          order: Int32, 
                          rc: Region[r]): Option[Node[v, r]] \ r with ToString[v] = match parent {
            case Some(node) => 
                let children = unwrap(node->children);
                let length = MutList.length(node->keys);
                if (length + 1 >= order) {
                    splitInternal(node, newKey, leftChild, rightChild, compare, order, rc)
                } else {
                    // Insert the new key first to know where to insert the node in the children
                    sortedInsert(newKey, node->keys, compare);
                    let index = binarySearch(newKey, node->keys, compare, true);
                    MutList.insert(rightChild, index, children);
                    None
                }
            case None =>  
                // In this case, leftChild is the root of the tree
                // and we must construct a new root node
                let children = MutList.empty(rc);
                let keys = MutList.empty(rc);
                MutList.push(leftChild, children); 
                MutList.push(rightChild, children);
                MutList.push(newKey, keys);
                let newRoot = new Node @ rc {
                    keys = keys,
                    children = Some(children),
                    parent = None,
                    next = None
                };
                leftChild->parent = Some(newRoot);
                rightChild->parent = Some(newRoot);
                Some(newRoot)
        }

    }

    mod BLinkTree {
        use Fixpoint.{Node, Compare, unwrap}
        use Fixpoint.MutList.binarySearch

        pub def empty(rc: Region[r], order: Int32): BLinkTree[v, r] \ r = 
            let node = new Node @ rc {
                keys = MutList.empty(rc), 
                children = None,
                parent = None, 
                next = None
            };
            new BLinkTree @ rc { 
                root = node,
                order = order,
                rc = rc 
            }

        pub def main3(): Unit \ IO = region rc {
            let compare: Int32 -> Int32 -> Comparison = x -> y -> {
                if (x < y) Comparison.LessThan
                else if (x > y) Comparison.GreaterThan
                else Comparison.EqualTo
            };
            let tree = empty(rc, 4);
            insert(tree, 6, compare);
            insert(tree, 16, compare);
            insert(tree, 24, compare);
            insert(tree, 8, compare);
            insert(tree, 2, compare);
            insert(tree, 1, compare);
            insert(tree, 9, compare);
            insert(tree, 10, compare);
            insert(tree, 17, compare);
            insert(tree, 26, compare);
            insert(tree, 39, compare);

            println("root: ${MutList.toVector(Node.keys(tree->root))}");
            def f(i: Int32, node: Node[Int32, rc]): Unit = {
                println("Child ${i}: ${MutList.toVector(Node.keys(node))} ")
            };
            MutList.forEachWithIndex(f, unwrap(Node.children(tree->root)))
        }       

        pub def insert(tree: BLinkTree[v, r], val: v, compare: Compare[v]): Unit \ r with ToString[v] = 
            let leaf = Node.traverse(tree->root, val, compare);
            let newRoot = Node.insertIntoLeaf(leaf, val, compare, tree->order, tree->rc);
            match newRoot {
                case Some(root) => tree->root = root
                case None => ()
            }

    }

}