instance ToString[Fixpoint.BTree2.Node[k, v, r]] with ToString[k], ToString[v] {

    pub def toString(x: Fixpoint.BTree2.Node[k, v, r]): String = 
        unchecked_cast(Fixpoint.BTree2.Node.toString(x, 0) as _ \ { })

}

// TODO: Possible optimzations: Instead of giving up as often as we do we could try test whether something changed
// TODO: Currently the arrays are of size order+1. Reorder the code to insert after the split.


// BTree with simple locking strategy: Lock node
mod Fixpoint.BTree2 {
    use Fixpoint.Lock
    use Fixpoint.Helpers.{unwrap, ptrEqual}

    pub struct BLinkTree[k, v, r] {
        mut root: Node[k, v, r],
        order:    Int32,
        rootLock: Lock[r],
        rc:       Region[r]
    }

    pub struct Node[k, v, r] {
        keys:       Array[k, r], // Acts as keys for internal nodes and values for leaves
        children:   Option[Array[Node[k, v, r], r]],
        leaves:     Option[Array[MutSet[v, r], r]],
        lock:       Lock[r],
        mut size:   Int32,      // Number of children / leaves 
        mut parent: Option[Node[k, v, r]],
        mut next:   Option[Node[k, v, r]]
    }     

    pub def main2(): Unit \ {IO} = region rc {
        let list = Array.empty(rc, 5);
        Array.put(4, 0, list);
        Array.put(6, 0, list);
        Array.put(8, 0, list);
        println(unchecked_cast(binarySearch(6, 5, list) as _ \ IO))
    }

    // Perform a binary search and return the index of `key` in `arr` if it exists.
    // Otherwise, return (-insertionPoint - 1). See Java binary search documentation for arrays.
    pub def binarySearch(key: v, length: Int32, arr: Array[v, r]): Int32 \ r with Order[v] = 
        if (length == 0) 
            -1
        else
            def f(l: Int32, r: Int32): Int32 \ r = {
                if (l <= r - 1) {
                    let m = (l + r) / 2;
                    match Array.get(m, arr) <=> key {
                        case Comparison.LessThan => f(m + 1, r)
                        case Comparison.GreaterThan => f(l, m)
                        case Comparison.EqualTo => m
                    }
                } else -l-1
            }; 
            f(0, length)

    pub def toInsertionPoint(i: Int32): Int32 = -i-1

    mod Node {
        use Fixpoint.Lock
        use Fixpoint.BTree2.{Node, binarySearch, toInsertionPoint, BLinkTree}
        use Fixpoint.Helpers.{unwrap, ptrEqual}

        pub def parent(node: Node[k, v, r]): Option[Node[k, v, r]] \ r = node->parent
        pub def next(node: Node[k, v, r]): Option[Node[k, v, r]] \ r = node->next
        pub def children(node: Node[k, v, r]): Option[Array[Node[k, v, r], r]]  = node->children
        pub def keys(node: Node[k, v, r]): Array[k, r] = node->keys
        pub def lock(node: Node[k, v, r]): Lock[r] = node->lock

        pub def toString(node: Node[k, v, r], indent: Int32): String \ r with ToString[k], ToString[v] = region rc {
            let indentString = String.repeat(indent, " ");
            match node->children {
                case Some(children) =>
                    let keysString = Array.join(",", Array.copyOfRange(rc, 0, node->size - 1, node->keys));
                    let childrenArr = Array.copyOfRange(rc, 0, node->size, children);
                    let childrenString = Array.foldLeft(a -> x -> "${a}${toString(x, indent+2)}", "", childrenArr);
                    "${indentString}Internal(${keysString})\n${childrenString}"
                case None => 
                    let keysString = Array.join(",", Array.copyOfRange(rc, 0, node->size, node->keys));
                    let leaves = Array.copyOfRange(rc, 0, node->size, unwrap(node->leaves));
                    let leavesString = Array.foldLeft(a -> x -> "${a}  ${indentString}Values(${MutSet.join(",", x)})\n", "", leaves);
                    "${indentString}Leaf(${keysString})\n${leavesString}"
            }
        }
        /// Traverse the tree until a leaf containing `val` is reached
        /// This function assumes that there is a lock on the node `root`
        //  The function provides a single read lock on the returned node
        pub def findLeaf(val: k, getRoot: Unit -> Node[k, v, r]  \ r): Node[k, v, r] \ r with Order[k], Order[v] = 
            // Traverse the tree while keeping the invariant that there is a node on cur. 
            // If aquiring a lock at any point fails release the locks you hold and retry from the top.
            def traverse(cur: Node[k, v, r]): Node[k, v, r] \ r =
                match cur->children {
                    case Some(children) =>
                        let index = binarySearch(val, cur->size - 1, cur->keys);
                        let childToVisit = if (index < 0)
                            Array.get(toInsertionPoint(index), children)
                        else
                            Array.get(index + 1, children);
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
                        node: Node[k, v, r],
                        rc: Region[r]): Unit \ r with Order[k], Order[v], ToString[k], ToString[v] =
            let size = node->size;
            let keys = node->keys;
            let leaves = unwrap(node->leaves);
            let index = binarySearch(key, size, keys);
            let set = if (index < 0) {
                let set = MutSet.empty(rc);
                let insertionPoint = toInsertionPoint(index);
                Array.insert(set, insertionPoint, size, leaves);
                Array.insert(key, insertionPoint, size, keys);
                node->size = size + 1;
                set
            }
            else 
                Array.get(index, leaves);
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
            if (node->size + 1 >= order)
                splitLeaf(node, key, val, order, rc)
            else {
                actualInsert(key, val, node, rc);
                Lock.unlock(node->lock);
                None
            }

// //        // Split `list` into two lists around index `i` such that `list` is truncated
// //        // to length `i` and the remaining values are inserted into a new list
//         def partition(i: Int32, list: Array[v, r], rc: Region[r]): Array[v, r] \ r = 
//             Array.copyOfRange(rc, i, Array.length(list), list)
//             // Array.truncate(i, list); 
//             // Array.toMutList(rc, rightArr)


        // (Lock) Invariants:
        //      On invocation, the thread has a lock on `node`.
        //      On return, the thread holds a lock on `node` and on `parent` given by `node->Some(parent)`
        // Try to lock the parent node. 
        def lockParent(node: Node[k, v, r]): Unit \ r with ToString[k], ToString[v] = match node->parent {
            case Some(parent) =>
                let parentLock = parent->lock;
                Lock.lock(parentLock);
                // If some thread had a lock on your parent and changed your parent pointer retry
                let isSame = ptrEqual(unwrap(node->parent), parent);
                if (not isSame) {
                    Lock.unlock(parentLock);
                    lockParent(node)
                } else ()
            case None => ()
        }

        // Split a leaf and push the middle key into the parent, potentially 
        // causing the parent to split and return a new root
        // (Lock) Invariants: 
        //   On invocation, the thread has a lock on `leftNode`.
        //   On return, the thread only holds a lock if the return value is Some. In that case it holds a lock on the new root and the old root.
        def splitLeaf(leftLeaf: Node[k, v, r], key: k, val: v, order: Int32, rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v], Order[k], Order[v] =
            lockParent(leftLeaf); // TODO: For performance move this to be last and update rightLeaf as necessary.
            let values = leftLeaf->keys;
            actualInsert(key, val, leftLeaf, rc);
            let mid = order / 2;
            
            let rightList = Array.empty(rc, order + 1);
            let rightLeaves = Array.empty(rc, order + 1);
            Array.copyInto(srcPos = mid, dstPos = 0, len = order - mid, src = values, dst = rightList);
            Array.copyInto(srcPos = mid, dstPos = 0, len = order - mid, src = unwrap(leftLeaf->leaves), dst = rightLeaves);
            // let rightList = partition(mid, values, rc);
            // let rightLeaves = partition(mid, unwrap(leftLeaf->leaves), rc);
            // Create a new leaf to store the right half
            let rightLeaf = new Node @ rc {
                keys = rightList,
                children = None,
                leaves = Some(rightLeaves),
                lock = Lock.mkLock(rc),
                size = leftLeaf->size - mid,
                parent = leftLeaf->parent,
                next = leftLeaf->next
            };
            // Update the old leaf's fields
            leftLeaf->next = Some(rightLeaf);
            leftLeaf->size = mid;
            // Push key up to parent
            let newKey = Array.get(0, rightList);
            Lock.lock(rightLeaf->lock);
            pushKeyToParent(leftLeaf->parent, newKey, leftLeaf, rightLeaf, order, rc)
        
        // (Lock) Invariants: 
        //   On invocation, the thread has a lock on `parent`.
        //   On return, the thread only holds a lock if the return value is Some. In that case it holds a lock on the new root and the old root.
        def fixParent(parent: Node[k, v, r], order: Int32, rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v], Order[k] =
            if (parent->size <= order) 
                None
            else
                let _ = lockParent(parent); // TODO: Move this to be last instruction and update new right as necessary.
                let children = unwrap(parent->children);
                let mid = (order + 1) / 2;
                let size = parent->size;
                let rightChildren = Array.empty(rc, order + 1);
                let rightKeys = Array.empty(rc, order);
                let rightKeyNum = size - mid;
                Array.copyInto(srcPos = mid, dstPos = 0, len = rightKeyNum, src = children, dst = rightChildren);
                Array.copyInto(srcPos = mid, dstPos = 0, len = rightKeyNum - 1, src = parent->keys, dst = rightKeys);
                // let rightChildren = partition(middle, children, rc);
                // let rightKeys = partition(middle, parent->keys, rc);
                // MutList.truncate(middle - 1, parent->keys);
                let rightNode = new Node @ rc {
                    keys = rightKeys,
                    children = Some(rightChildren),
                    leaves = None,
                    lock = Lock.mkLock(rc),
                    size = size - mid,
                    parent = parent->parent,
                    next = parent->next
                };
                parent->size = mid;
                parent->next = Some(rightNode);
                // Array.forEach(child -> child->parent = Some(rightNode), rightChildren);
                Array.forEachWithIndex(i -> child -> 
                    if (i < rightKeyNum) 
                        child->parent = Some(rightNode) 
                    else (), rightChildren);
                Lock.lock(rightNode->lock); // pushKeyToParent requires a lock
                pushKeyToParent(parent->parent, Array.get(0, rightNode->keys), parent, rightNode, order, rc)

        // (Lock) Invariants: 
        //   On invocation, the thread has a lock on `parent`, `leftChild` and `rightChild`.
        //   On return, the thread only holds a lock if the return value is Some. In that case it holds a lock on the new root and the old root.
        def pushKeyToParent(parent: Option[Node[k, v, r]], 
                          newKey: k, 
                          leftChild: Node[k, v, r],
                          rightChild: Node[k, v, r],
                          order: Int32, 
                          rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v], Order[k] = match parent {
            case Some(node) => 
                let children = unwrap(node->children);
                let index = binarySearch(newKey, node->size - 1, node->keys);
                if (index < 0) {
                    let insertionPoint = toInsertionPoint(index);
                    let size = node->size;
                    if(insertionPoint == size - 1) {
                        Array.put(newKey, insertionPoint, node->keys);
                        Array.put(rightChild, insertionPoint + 1, children)
                    } else {
                        Array.insert(newKey, insertionPoint, node->size, node->keys);
                        Array.insert(rightChild, insertionPoint + 1, node->size + 1, children)
                    };
                    node->size = size + 1;
                    None
                } else bug!("Key should be unique");
                Lock.unlock(leftChild->lock);
                Lock.unlock(rightChild->lock);
                fixParent(node, order, rc)
            case None =>
                // In this case, leftChild is the root of the tree
                // and we must construct a new root node
                let children = Array.empty(rc, order + 1); // TODO: Dont allocate one extra cell
                let keys = Array.empty(rc, order);
                Array.put(leftChild, 0, children);
                Array.put(rightChild, 1, children);
                Array.put(newKey, 0, keys);
                let newRoot = new Node @ rc {
                    keys = keys,
                    children = Some(children),
                    leaves = None,
                    lock = Lock.mkLock(rc),
                    size = 2,
                    parent = None,
                    next = None
                };
                Lock.lock(newRoot->lock);
                leftChild->parent = Some(newRoot);
                rightChild->parent = Some(newRoot);
                Lock.unlock(rightChild->lock);
                Some(newRoot)
        }

        pub def rangeQueryWith(f: k -> v -> Unit \ r0, min: k, max: k, getRoot: Unit -> Node[k, v, r1] \ r1): Unit \ {r0, r1} with ToString[k], ToString[v], Order[k], Order[v] =
            let minLeaf = findLeaf(min, getRoot);
            let index = binarySearch(min, minLeaf->size - 1, minLeaf->keys);
            if(index < 0) {
                let insertionPoint = toInsertionPoint(index);
                if (insertionPoint <= minLeaf->size) 
                    traverseRight(f, insertionPoint, max, minLeaf)
                 else ()
            } else 
            // if(index < 0) traverseRight(f, toInsertionPoint(index), max, minLeaf) else 
                traverseRight(f, index, max, minLeaf)

        def traverseRight(f: k -> v -> Unit \ r0, index: Int32, max: k, node: Node[k, v, r1]): Unit \ {r0, r1} with ToString[k], ToString[v], Order[k], Order[v] =
            let k = Array.get(index, node->keys);
            if(k <= max) {
                MutSet.forEach(v -> f(k, v), Array.get(index, unwrap(node->leaves)));
                if(index < node->size)
                    traverseRight(f, index + 1, max, node)
                else match node->next {
                    case Some(next) => traverseRight(f, 0, max, next)
                    case None => ()
                }
            } else ()
            
    }

    mod BLinkTree {
        use Fixpoint.Lock
        use Fixpoint.BTree2.Node
        use Fixpoint.Helpers.unwrap
        import java.lang.System

        pub def empty(rc: Region[r], order: Int32): BLinkTree[k, v, r] \ r with Order[k] = 
            if (order <= 2)
                bug!("order of tree must be at least 3")
            else
                let node = new Node @ rc {
                    keys = Array.empty(rc, order), 
                    children = None,
                    leaves = Some(Array.empty(rc, order + 1)),
                    lock = Lock.mkLock(rc),
                    size = 0,
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
            let newRoot = Node.insertIntoLeaf(leaf, key, val, tree->order, tree->rc);
            match newRoot {
                case Some(root) => 
                    Lock.lock(tree->rootLock);
                    let oldRoot = tree->root;
                    tree->root = root;
                    Lock.unlock(tree->rootLock);
                    Lock.unlock(Node.lock(oldRoot));
                    Lock.unlock(Node.lock(root))
                case None => ()
            }

        pub def rangeQueryWith(f: k -> v -> Unit \ ef, min: k, max: k, tree: BLinkTree[k, v, r]): Unit \ {r, ef} with Order[k], Order[v], ToString[v], ToString[k] = 
            let getRoot = () -> getRoot(tree);
            Node.rangeQueryWith(f, min, max, getRoot)

        // Locks the root and provides a lock on the root node.
        pub def getRoot(tree: BLinkTree[k, v, r]): Node[k, v, r] \ r = 
            Lock.lock(tree->rootLock);
            let root = tree->root;
            let success = Lock.tryLock(Node.lock(root));
            Lock.unlock(tree->rootLock);
            if(success) 
                root
            else {
                // Wait for the thread that was operating on the root to finish
                Lock.lock(Node.lock(root));
                Lock.unlock(Node.lock(root));
                getRoot(tree)
            }
            
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
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 0, 12, tree);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 4, 6, tree);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 5, 12, tree);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 11, 12, tree);
            // rangeQueryWith(k -> v -> println("${k}: ${v}"), 11, 0, tree);
            ()
        }

        pub def main4(): Unit \ IO = region rc {
            let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 5);
            List.forEach(i -> insert(i, i+1, tree), List.range(0, 1000));
            // insert(5, 10, tree);
            // insert(6, 11, tree);
            // insert(7, 11, tree);
            println(tree->root);
            // println("");
            ()
        }

        pub def main5(): Unit \ IO = region rc {
            let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 3);
            insert(5, 10, tree);
            insert(6, 11, tree);
            insert(7, 11, tree);
            println(tree->root);
            // println("");
            ()
        }

        pub def main6(): Unit \ IO = region rc {
            let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 3);
            insert(5, 10, tree);
            insert(6, 11, tree);
            insert(7, 12, tree);
            insert(8, 13, tree);
            println(tree->root);
            // println("");
            ()
        }
    }
}