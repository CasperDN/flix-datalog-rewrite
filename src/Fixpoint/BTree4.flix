// instance ToString[Fixpoint.BTree4.Node[k, v, r]] with ToString[k], ToString[v] {

//     pub def toString(x: Fixpoint.BTree4.Node[k, v, r]): String = 
//         unchecked_cast(Fixpoint.BTree4.Node.toString(x, 0) as _ \ { })

// }

// BTree with simple locking strategy: Lock node
mod Fixpoint.BTree4 {
    use Fixpoint.Lock
    import java.util.concurrent.atomic.AtomicReferenceArray

    
    def unwrap(x: Option[a]): a = match x {
        case Some(v) => v
        case None => bug!("Attempted unwrapping None")
    }  

    pub struct BLinkTree[k, v, r] {
        mut root: Node[k, v, r],
        order:    Int32,
        rootLock: Lock.Lock[r],
        rc:       Region[r]
    }

    pub struct Node[k, v, r] {
        keys:       AtomicReferenceArray, // Acts as keys for internal nodes and values for leaves
        children:   Option[AtomicReferenceArray], // Option[Node[k, v, r]]
        leaves:     Option[AtomicReferenceArray], // Option[MutList[MutSet[v, r], r]]
        lock:       Lock.Lock[r],
        mut parent: Option[Node[k, v, r]],
        mut next:   Option[Node[k, v, r]]
    }

    pub def main2(): Unit \ {IO} = region rc {
        let list = MutList.empty(rc);
        MutList.push(2, list);
        MutList.push(4, list);
        MutList.push(6, list);
        MutList.push(8, list);
        // let compare: Int32 -> Int32 -> Comparison = x -> y -> {
        //     if (x < y) Comparison.LessThan
        //     else if (x > y) Comparison.GreaterThan
        //     else Comparison.EqualTo
        // };
        println(unchecked_cast(binarySearch(6, list) as _ \ IO))
    }

    // Perform a binary search and return the index of `key` in `list` if it exists.
    // Otherwise, return (-insertionPoint - 1). See Java binary search documentation for arrays.
    pub def binarySearch(key: v, list: MutList[v, r]): Int32 \ r with Order[v] = 
        if (MutList.isEmpty(list)) 
            -1
        else
            def f(l: Int32, r: Int32): Int32 \ r = {
                if (l <= r - 1) {
                    let m = (l + r) / 2;
                    let cur = MutList.rawGet(m, list);
                    match Order.compare(cur, key) {
                        case Comparison.LessThan => f(m + 1, r)
                        case Comparison.GreaterThan => f(l, m)
                        case Comparison.EqualTo => m
                    }
                } else -l-1
            }; 
            f(0, MutList.length(list))

    pub def toInsertionPoint(i: Int32): Int32 = -i-1

    mod Node {
        use Fixpoint.Lock
        use Fixpoint.BTree4.{Node, unwrap, binarySearch, toInsertionPoint, BLinkTree}
        import java.util.concurrent.locks.ReentrantReadWriteLock
    import java.util.concurrent.atomic.AtomicReferenceArray

        pub def parent(node: Node[k, v, r]): Option[Node[k, v, r]] \ r = node->parent
        pub def next(node: Node[k, v, r]): Option[Node[k, v, r]] \ r = node->next
        pub def children(node: Node[k, v, r]): Option[AtomicReferenceArray]  = node->children
        pub def keys(node: Node[k, v, r]): AtomicReferenceArray = node->keys
        pub def lock(node: Node[k, v, r]): Lock.Lock[r] = node->lock

        // pub def toString(node: Node[k, v, r], indent: Int32): String \ r with ToString[k], ToString[v] = 
        //     let indentString = String.repeat(indent, " ");
        //     let keysString = MutList.join(",", node->keys);
        //     match node->children {
        //         case Some(children) =>
        //             let childrenString = MutList.foldLeft(a -> x -> "${a}${toString(x, indent+2)}", "", children);
        //             "${indentString}Internal(${keysString})\n${childrenString}"
        //         case None => 
        //             let leaves = unwrap(node->leaves);
        //             let leavesString = MutList.foldLeft(a -> x -> "${a}  ${indentString}Values(${MutSet.join(",", x)})\n", "", leaves);
        //             "${indentString}Leaf(${keysString})\n${leavesString}"
        //     }

        /// Traverse the tree until a leaf containing `val` is reached
        /// This function assumes that there is a lock on the node `root`
        //  The function provides a single read lock on the returned node
        pub def findLeaf(val: k, getRoot: Unit -> Node[k, v, r]  \ r): Node[k, v, r] \ r with Order[k], Order[v] = 
            // Traverse the tree while keeping the invariant that there is a node on cur. 
            // If aquiring a lock at any point fails release the locks you hold and retry from the top.
            def traverse(cur: Node[k, v, r]): Node[k, v, r] \ r =
                match cur->children {
                    case Some(children) =>
                        let index = binarySearch(val, cur->keys);
                        let childToVisit = if (index < 0)
                            MutList.rawGet(toInsertionPoint(index), children)
                        else 
                            MutList.rawGet(index + 1, children);
                        // Try to get a read-lock on the next child
                        let childLock = childToVisit->lock;
                        let success = Lock.tryLock(childLock);
                        Lock.unlock(cur->lock);
                        if(success)
                            // Unlock the current node i.e. the parent of `childToVisit`
                            traverse(childToVisit)
                        else {
                            // Give up and restart the attempt. 
                            // To allow for the writer we encountered to grab the lock 
                            // on the node readLock the child node as a wait operation.
                            Lock.lock(childLock);
                            Lock.unlock(childLock);
                            traverse(getRoot())
                        }
                    case None => cur
                };
        traverse(getRoot())
                

        def actualInsert(key: k, 
                                 val: v, 
                                 keys: MutList[k, r], 
                                 leaves: MutList[MutSet[v, r], r], 
                                 rc: Region[r]): Unit \ r with Order[k], Order[v] =
            let index = binarySearch(key, keys);
            let set = if (index < 0) 
                let set = MutSet.empty(rc);
                let insertionPoint = toInsertionPoint(index);
                MutList.insert(set, insertionPoint, leaves);
                MutList.insert(key, insertionPoint, keys);
                set
            else
                MutList.rawGet(index, leaves);
            MutSet.add(val, set)

        // Insert a value into a leaf, potentially causing a split and returning a new root
        // (Lock) Invariants: 
        //      On invocation, the thread has a lock on `node`.
        //      On return, the thread only holds a lock on `Some(node)`
        pub def insertIntoLeaf(node: Node[k, v, r], 
                               key: k, 
                               val: v, 
                               order: Int32, 
                               rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v], Order[k], Order[v] = 
            let length = MutList.length(node->keys);
            if (length + 1 >= order)
                splitLeaf(node, key, val, order, rc)
            else {
                actualInsert(key, val, node->keys, unwrap(node->leaves), rc);
                Lock.unlock(node->lock);
                None
            }

        // Split `list` into two lists around index `i` such that `list` is truncated
        // to length `i` and the remaining values are inserted into a new list
        def partition(i: Int32, list: MutList[v, r], rc: Region[r]): MutList[v, r] \ r = 
            let arr = MutList.toArray(rc, list);
            let rightArr = Array.copyOfRange(rc, i, MutList.length(list), arr);
            MutList.truncate(i, list); 
            Array.toMutList(rc, rightArr)

        // Split a leaf and push the middle key into the parent, potentially 
        // causing the parent to split and return a new root
        // (Lock) Invariants: 
        //      On invocation, the thread has a lock on `leftNode`.
        //      On return, the thread only holds a lock on `Some(node)`
        def splitLeaf(leftLeaf: Node[k, v, r], key: k, val: v, order: Int32, rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v], Order[k], Order[v] = 
            let values = leftLeaf->keys;
            actualInsert(key, val, leftLeaf->keys, unwrap(leftLeaf->leaves), rc);
            let rightList = partition(order / 2, values, rc);            
            let rightLeaves = partition(order / 2, unwrap(leftLeaf->leaves), rc);
            // unchecked_cast(println("leftList: ${MutList.toVector(values)}") as _ \ r);
            // unchecked_cast(println("rightList: ${MutList.toVector(rightList)}") as _ \ r);
            // Create a new leaf to store the right half
            let rightLeaf = new Node @ rc {
                keys = rightList,
                children = None,
                leaves = Some(rightLeaves),
                lock = Lock.mkLock(rc),
                parent = leftLeaf->parent,
                next = leftLeaf->next
            };
            // Update the old leaf's fields
            leftLeaf->next = Some(rightLeaf);
            // Push key up to parent
            let newKey = unwrap(MutList.head(rightList));
            pushKeyToParent(leftLeaf->parent, newKey, leftLeaf, rightLeaf, order, rc)

        def fixParent(parent: Node[k, v, r], order: Int32, rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v], Order[k] =
            let children = unwrap(parent->children);
            if (MutList.length(children) <= order) None else
            let middle = (order + 1) / 2;
            let rightChildren = partition(middle, children, rc);
            let rightKeys = partition(middle, parent->keys, rc);
            MutList.truncate(middle - 1, parent->keys);
            let rightNode = new Node @ rc {
                keys = rightKeys,
                children = Some(rightChildren),
                leaves = None,
                lock = Lock.mkLock(rc),
                parent = parent->parent,
                next = parent->next
            };
            parent->next = Some(rightNode);
            MutList.forEach(child -> child->parent = Some(rightNode), rightChildren);
            pushKeyToParent(parent->parent, MutList.rawGet(0, rightNode->keys), parent, rightNode, order, rc)
    

        // Problem encountered: We wish to get the parent. We therefore get the parent pointer and lock it. 
        // Someone else might have split the parent between our read and our acquiring the lock. We cannot compare pointers to discover this...
        def pushKeyToParent(parent: Option[Node[k, v, r]], 
                          newKey: k, 
                          leftChild: Node[k, v, r],
                          rightChild: Node[k, v, r],
                          order: Int32, 
                          rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v], Order[k] = match parent {
            case Some(node) => 
                let children = unwrap(node->children);
                let index = binarySearch(newKey, node->keys);
                if (index < 0) {
                    let insertionPoint = toInsertionPoint(index);
                    MutList.insert(newKey, insertionPoint, node->keys);
                    MutList.insert(rightChild, insertionPoint + 1, children);
                    None
                } else bug!("Key should be unique");
                fixParent(node, order, rc)
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
                    leaves = None,
                    lock = Lock.mkLock(rc),
                    parent = None,
                    next = None
                };
                leftChild->parent = Some(newRoot);
                rightChild->parent = Some(newRoot);
                Some(newRoot)
        }


        pub def rangeQueryWith(f: k -> v -> Unit \ r0, min: k, max: k, getRoot: Unit -> Node[k, v, r1] \ r1): Unit \ {r0, r1} with ToString[k], ToString[v], Order[k], Order[v] =
            let minLeaf = findLeaf(min, getRoot);
            let index = binarySearch(min, minLeaf->keys);
            if(index < 0) {
                let insertionPoint = toInsertionPoint(index);
                if (insertionPoint < MutList.length(minLeaf->keys)) 
                    traverseRight(f, toInsertionPoint(index), max, minLeaf)
                 else ()
            } else 
            // if(index < 0) traverseRight(f, toInsertionPoint(index), max, minLeaf) else 
                traverseRight(f, index, max, minLeaf)

        def traverseRight(f: k -> v -> Unit \ r0, index: Int32, max: k, node: Node[k, v, r1]): Unit \ {r0, r1} with ToString[k], ToString[v], Order[k], Order[v] =
            let k = MutList.rawGet(index, node->keys);
            if(k <= max) {
                MutSet.forEach(v -> f(k, v), MutList.rawGet(index, unwrap(node->leaves)));
                if(index + 1 < MutList.length(node->keys))
                    traverseRight(f, index + 1, max, node)
                else match node->next {
                    case Some(next) => traverseRight(f, 0, max, next)
                    case None => ()
                }
            } else ()
            
    }

    mod BLinkTree {
        use Fixpoint.Lock
        use Fixpoint.BTree4.{Node, unwrap}
        import java.lang.System

        pub def main3(): Unit \ {IO, NonDet} = region rc {
            let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 8);
            let start = System.nanoTime();
            List.forEach(i -> insert(i, Int32.modulo(Random.runWithIO(Random.randomInt32), 30), tree), List.shuffle(List.range(0, 50)));
            let time = System.nanoTime() - start;
            println("Time: ${time / 1000000i64} ms");
            // List.forEach(i -> insert(i, Int32.modulo(Random.runWithIO(Random.randomInt32), 30), tree), List.shuffle(List.range(0, 50)));

            insert(5, 10, tree);
            insert(5, 7, tree);
            insert(6, 8, tree);
            insert(10, 2, tree);
            insert(1, 4, tree);
            // println(tree->root);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 0, -2, tree);
            rangeQueryWith(k -> v -> println("${k}: ${v}"), 0, 12, tree);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 4, 6, tree);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 5, 12, tree);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 11, 12, tree);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 11, 0, tree);
            ()
        }


        pub def empty(rc: Region[r], order: Int32): BLinkTree[k, v, r] \ r with Order[k] = 
            if (order <= 2) 
                bug!("order of tree must be at least 3")
            else
                let node = new Node @ rc {
                    keys = MutList.empty(rc), 
                    children = None,
                    leaves = Some(MutList.empty(rc)),
                    lock = Lock.mkLock(rc),
                    parent = None, 
                    next = None
                };
                new BLinkTree @ rc { 
                    root = node,
                    order = order,
                    rootLock = Lock.mkLock(rc),
                    rc = rc 
                }
    

        pub def insert(key: k, val: v, tree: BLinkTree[k, v, r]): Unit \ r with ToString[k], ToString[v], Order[k], Order[v] = 
            let getRoot: Unit -> Node[k, v, r] \ r = () -> getRoot(tree);
            let leaf = Node.findLeaf(key, getRoot);
            // Node.lock(leaf);
            let newRoot = Node.insertIntoLeaf(leaf, key, val, tree->order, tree->rc);
            match newRoot {
                case Some(root) => 
                    Lock.lock(tree->rootLock);
                    tree->root = root;
                    Lock.unlock(tree->rootLock);
                    Lock.unlock(Node.lock(root))
                case None => ()
            }

        pub def rangeQueryWith(f: k -> v -> Unit \ ef, min: k, max: k, tree: BLinkTree[k, v, r]): Unit \ {r, ef} with Order[k], Order[v], ToString[v], ToString[k] = 
            let getRoot = () -> getRoot(tree);
            Node.rangeQueryWith(f, min, max, getRoot)

        pub def getRoot(tree: BLinkTree[k, v, r]): Node[k, v, r] \ r = 
            Lock.lock(tree->rootLock);
            let root = tree->root;
            let success = Lock.tryLock(Node.lock(root));
            Lock.unlock(tree->rootLock);
            if(success) 
                root
            else {
                Lock.lock(Node.lock(root));
                getRoot(tree)
            }
            
    }
}