instance ToString[Fixpoint.BLTNode[k, v, r]] with ToString[k], ToString[v] {
    pub def toString(x: Fixpoint.BLTNode[k, v, r]): String = 
        unchecked_cast(Fixpoint.BLTNode.toString(x, 0) as _ \ { })
}

// TODO: Possible optimzations: Instead of giving up as often as we do we could try test whether something changed
// TODO: Need non-concurrent methods that dont use locks for faster traversal etc.

// BTree with simple locking strategy: Lock node
// Assumptions about use: At any given time there will only EITHER be insertions or reads/range queries.
// If this invariant is broken 

mod Fixpoint {
    use Fixpoint.Lock

    pub struct BLinkTree[k, v, r] {
        mut root: BLTNode[k, v, r],
        order:    Int32,
        rootLock: Lock[r],
        rc:       Region[r]
    }

    pub struct BLTNode[k, v, r] {
        keys:       Array[k, r], // Acts as keys for internal nodes and values for leaves
        children:   Option[Array[BLTNode[k, v, r], r]],
        values:     Option[Array[MutSet[v, r], r]],
        lock:       Lock[r],
        mut size:   Int32,      // Number of children / values 
        mut parent: Option[BLTNode[k, v, r]],
        mut next:   Option[BLTNode[k, v, r]]
    }
}

    // pub def main5(): Unit \ { IO } = region rc {
    //     let list = Array.empty(rc, 5);
    //     Array.put(4, 0, list);
    //     Array.put(6, 0, list);
    //     Array.put(8, 0, list);
    //     println(unchecked_cast(binarySearch(6, 5, list) as _ \ IO))
    // }

mod Fixpoint.BLTNode {
    use Fixpoint.BLTNode
    use Fixpoint.Helpers.{unwrap, ptrEqual, toInsertionPoint, binarySearch}
    use Fixpoint.Lock

    pub def parent(node: BLTNode[k, v, r]): Option[BLTNode[k, v, r]] \ r = node->parent
    pub def next(node: BLTNode[k, v, r]): Option[BLTNode[k, v, r]] \ r = node->next
    pub def children(node: BLTNode[k, v, r]): Option[Array[BLTNode[k, v, r], r]]  = node->children
    pub def values(node: BLTNode[k, v, r]): Option[Array[MutSet[v, r], r]]  = node->values
    pub def keys(node: BLTNode[k, v, r]): Array[k, r] = node->keys
    pub def size(node: BLTNode[k, v, r]): Int32 \ r  = node->size

    pub def lock(node: BLTNode[k, v, r]): Lock[r] = node->lock

    pub def toString(node: BLTNode[k, v, r], indent: Int32): String \ r with ToString[k], ToString[v] = region rc {
        let indentString = String.repeat(indent, " ");
        match node->children {
            case Some(children) =>
                let keysString = Array.join(",", Array.copyOfRange(rc, 0, node->size - 1, node->keys));
                let childrenArr = Array.copyOfRange(rc, 0, node->size, children);
                let childrenString = Array.foldLeft(a -> x -> "${a}${toString(x, indent+2)}", "", childrenArr);
                "${indentString}Internal(${keysString})\n${childrenString}"
            case None => 
                let keysString = Array.join(",", Array.copyOfRange(rc, 0, node->size, node->keys));
                let values = Array.copyOfRange(rc, 0, node->size, unwrap(node->values));
                let valuesString = Array.foldLeft(a -> x -> "${a}  ${indentString}Values(${MutSet.join(",", x)})\n", "", values);
                "${indentString}Leaf(${keysString})\n${valuesString}"
        }
    }

    /// Like `findLeaf` but assumes no concurrency
    pub def findLeafUnsafe(key: k, node: BLTNode[k, v, r]): BLTNode[k, v, r] \ r with Order[k], Order[v] = 
        match node->children {
            case Some(children) => 
                let index = binarySearch(key, node->size - 1, node->keys);
                let childToVisit = if (index < 0)
                    Array.get(toInsertionPoint(index), children)
                else
                    Array.get(index + 1, children);
                findLeafUnsafe(key, childToVisit)
            case None => node
        }

    /// Traverse the tree until a leaf containing `val` is reached
    /// This function assumes that there is a lock on the node `root`
    /// The function provides a single read lock on the returned node
    pub def findLeaf(key: k, getRoot: Unit -> BLTNode[k, v, r]  \ r): BLTNode[k, v, r] \ r with Order[k], Order[v], ToString[k], ToString[v] = 
        // Traverse the tree while keeping the invariant that there is a node on cur. 
        // If aquiring a lock at any point fails release the locks you hold and retry from the top.
        def traverse(cur: BLTNode[k, v, r]): BLTNode[k, v, r] \ r =
            match cur->children {
                case Some(children) =>
                    let index = binarySearch(key, cur->size - 1, cur->keys);
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
    
    pub def isEmpty(node: BLTNode[k, v, r]): Bool \ r = node->size == 0

    pub def contains(key: k, val: v, node: BLTNode[k, v, r]): Bool \ r with Order[k], Order[v], ToString[k], ToString[v] = 
        match node->values {
            case Some(values) => 
                let index1 = binarySearch(key, node->size, node->keys);
                if (index1 < 0) 
                    false
                else
                    let set = Array.get(index1, values);
                    MutSet.memberOf(val, set)
            case None => bug!("The contains method on nodes should only be used on leaves")
        }

    def actualInsertLeaf(
            key: k,
            val: v,
            insertionPoint: Int32,
            node: BLTNode[k, v, r],
            rc: Region[r]): Unit \ r with Order[k], Order[v], ToString[k], ToString[v] =
        let size = node->size;
        let set = MutSet.empty(rc);
        MutSet.add(val, set);
        Array.insert(set, insertionPoint, size, unwrap(node->values));
        Array.insert(key, insertionPoint, size, node->keys);
        node->size = size + 1


    def actualInsertInternal(
            key: k,
            child: BLTNode[k, v, r],
            insertionPoint: Int32,
            node: BLTNode[k, v, r]): Unit \ r with Order[k], Order[v], ToString[k], ToString[v] =
        let size = node->size;
        let children = unwrap(node->children);
        Array.insert(child, insertionPoint + 1, size, children);
        // if(insertionPoint != 0) {
            Array.insert(key, insertionPoint, size, node->keys);
        // } else ();
        node->size = size + 1

    /// Insert key-value pair `(key, val)` into the leaf `node`, 
    /// potentially causing a split and returning a new root
    /// (Lock) Invariants: 
    ///      On invocation, the thread has a lock on `node`.
    ///      On return, the thread only holds a lock on `Some(node)`
    pub def insertIntoLeaf(
            node: BLTNode[k, v, r], 
            key: k,
            val: v,
            order: Int32,
            rc: Region[r]): Option[BLTNode[k, v, r]] \ r with ToString[k], ToString[v], Order[k], Order[v] =
        let size = node->size;
        let index = binarySearch(key, size, node->keys);
        if (index >= 0) 
            let set = Array.get(index, unwrap(node->values));
            MutSet.add(val, set);
            None
        else
            let insertionPoint = toInsertionPoint(index);
            if (size < order) {
                actualInsertLeaf(key, val, insertionPoint, node, rc);
                None
            } else 
                splitLeaf(node, key, val, insertionPoint, order, rc)

    // (Lock) Invariants:
    //      On invocation, the thread has a lock on `node`.
    //      On return, the thread holds a lock on `node` and on `parent` given by `node->Some(parent)`
    // Try to lock the parent node. 
    def lockParent(node: BLTNode[k, v, r]): Unit \ r with ToString[k], ToString[v] = match node->parent {
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

    // Split a `leftLeaf` into two leaves and push the middle key into the parent,  
    // potentially causing the parent to split and return a new root
    // (Lock) Invariants: 
    //   On invocation, the thread has a lock on `leftNode`.
    //   On return, the thread only holds a lock if the return value is Some. In that case it holds a lock on the new root and the old root.
    def splitLeaf(
            leftLeaf: BLTNode[k, v, r],
            key: k,
            val: v,
            insertionPoint: Int32,
            order: Int32,
            rc: Region[r]): Option[BLTNode[k, v, r]] \ r with ToString[k], ToString[v], Order[k], Order[v] =
        lockParent(leftLeaf); // TODO: For performance move this to be last and update rightLeaf as necessary.
        let prev_mid = order / 2;
        let (mid, insertInLeft) = if (insertionPoint <= prev_mid) (prev_mid, true) else (prev_mid + 1, false);
        let rightKeys = Array.empty(rc, order);
        let rightValues = Array.empty(rc, order);
        Array.copyInto(srcPos = mid, dstPos = 0, len = order - mid, src = leftLeaf->keys, rightKeys);
        Array.copyInto(srcPos = mid, dstPos = 0, len = order - mid, src = unwrap(leftLeaf->values), rightValues);
        // Create a new leaf to store the right half
        let rightLeaf = new BLTNode @ rc {
            keys = rightKeys,
            children = None,
            values = Some(rightValues),
            lock = Lock.mkLock(rc),
            size = leftLeaf->size - mid,
            parent = leftLeaf->parent,
            next = leftLeaf->next
        };
        // Update the old leaf's fields
        leftLeaf->next = Some(rightLeaf);
        leftLeaf->size = mid;

        if (insertInLeft) actualInsertLeaf(key, val, insertionPoint, leftLeaf, rc) 
        else actualInsertLeaf(key, val, insertionPoint - mid, rightLeaf, rc);
        // Push key up to parent
        Lock.lock(rightLeaf->lock);
        pushKeyToParent(leftLeaf->parent, leftLeaf, rightLeaf, Array.get(0, rightLeaf->keys), order, rc)
    
    // (Lock) Invariants: 
    //   On invocation, the thread has a lock on `parent`.
    //   On return, the thread only holds a lock if the return value is Some. In that case it holds a lock on the new root and the old root.
    def splitParent(
            parent: BLTNode[k, v, r],
            insertedChild: BLTNode[k, v, r],
            insertionPoint: Int32,
            newKey: k,
            order: Int32,
            rc: Region[r]): Option[BLTNode[k, v, r]] \ r with ToString[k], ToString[v], Order[k], Order[v] =
        lockParent(parent); // TODO: Move this to be last instruction and update new right as necessary.
        // let newKey = Array.get(0, insertedChild->keys);
        let prev_mid = order / 2;
        let (mid, insertInLeft) = if (insertionPoint >= prev_mid) (prev_mid + 1, false) else (prev_mid, true);
        let rightKeys = Array.empty(rc, order - 1);
        let rightChildren = Array.empty(rc, order);
        let rightSizeWithoutNew = parent->size - mid;
        // Copy while omitting the middle key. If insertionPoint == prev_mid exclude the new key.
        parent->size = mid;
        let (rightSize, keyToPass) = if (insertInLeft) {
            let keyToPass_ = Array.get(mid - 1, parent->keys);
            // No problems. Just copy everything from mid and forward. Finish by inserting the new element in old node.
            Array.copyInto(srcPos = mid, dstPos = 0, len = rightSizeWithoutNew - 1, src = parent->keys, rightKeys);
            Array.copyInto(srcPos = mid, dstPos = 0, len = rightSizeWithoutNew, src = unwrap(parent->children), rightChildren);
            // parent->size = parent->size;
            actualInsertInternal(newKey, insertedChild, insertionPoint, parent);
            (rightSizeWithoutNew, keyToPass_)
        } else {
            // Can avoid somewhat. Just only insert in right if it will not be the first element.
            let keyToPass_ = if(insertionPoint + 1 == mid) {
                // If insertionPoint is the first element copy all old keys and old elements and insert new child at 0.
                Array.copyInto(srcPos = mid - 1, dstPos = 0, len = rightSizeWithoutNew, src = parent->keys, rightKeys);
                Array.copyInto(srcPos = mid, dstPos = 1, len = rightSizeWithoutNew, src = unwrap(parent->children), rightChildren);
                Array.put(insertedChild, 0, rightChildren);
                newKey
            } else {
                let childIndexInRight = insertionPoint + 1 - mid;
                Array.copyInto(srcPos = mid, dstPos = 0, len = childIndexInRight - 1, src = parent->keys, rightKeys);
                Array.copyInto(srcPos = mid, dstPos = 0, len = childIndexInRight, src = unwrap(parent->children), rightChildren);
                Array.put(newKey, childIndexInRight - 1, rightKeys);
                Array.put(insertedChild, childIndexInRight, rightChildren);
                // If insertionPoint is the last index we are done, otherwise insert rest of list.
                if(childIndexInRight != rightSizeWithoutNew) {
                    // TODO: -1?
                    Array.copyInto(srcPos = mid + childIndexInRight - 1, dstPos = childIndexInRight, len = rightSizeWithoutNew - childIndexInRight, src = parent->keys, rightKeys);
                    Array.copyInto(srcPos = mid + childIndexInRight, dstPos = childIndexInRight + 1, len = rightSizeWithoutNew - childIndexInRight, src = unwrap(parent->children), rightChildren)
                } else ();
                Array.get(mid - 1, parent->keys)
            };
            (rightSizeWithoutNew + 1, keyToPass_)
        };


        // Array.copyInto(srcPos = mid - 1, dstPos = 0, len = rightSize - 1, src = parent->keys, rightKeys);
        // Array.copyInto(srcPos = mid, dstPos = 0, len = rightSize, src = unwrap(parent->children), rightChildren);
        let rightNode = new BLTNode @ rc {
            keys = rightKeys,
            children = Some(rightChildren),
            values = None,
            lock = Lock.mkLock(rc),
            size = rightSize,
            parent = parent->parent,
            next = parent->next
        };
        // parent->size = mid;
        parent->next = Some(rightNode);
        // if (insertInLeft) actualInsertInternal(newKey, insertedChild, insertionPoint, parent)
        // else actualInsertInternal(newKey, insertedChild, insertionPoint - mid, rightNode);
        Array.forEachWithIndex(i -> child -> 
            if (i < rightSize)
                child->parent = Some(rightNode)
            else (), rightChildren);
        Lock.lock(rightNode->lock); // pushKeyToParent expects a lock on the parent
        pushKeyToParent(parent->parent, parent, rightNode, keyToPass, order, rc)

    // (Lock) Invariants: 
    //   On invocation, the thread has a lock on `parent`, `leftChild` and `rightChild`.
    //   On return, the thread only holds a lock if the return value is Some. In that case it holds a lock on the new root and the old root.
    def pushKeyToParent(
            parent: Option[BLTNode[k, v, r]], 
            leftChild: BLTNode[k, v, r],
            rightChild: BLTNode[k, v, r],
            newKey: k,
            order: Int32, 
            rc: Region[r]): Option[BLTNode[k, v, r]] \ r with ToString[k], ToString[v], Order[k], Order[v] =
        match parent {
        case Some(node) =>
            let children = unwrap(node->children);
            let insertionPoint = toInsertionPoint(binarySearch(newKey, node->size - 1, node->keys));
            let size = node->size;
            if(size < order) {
                Array.insert(newKey, insertionPoint, size - 1, node->keys);
                Array.insert(rightChild, insertionPoint + 1, size, children);
                node->size = size + 1;
                Lock.unlock(leftChild->lock);
                Lock.unlock(rightChild->lock);
                None
            } else {
                Lock.unlock(leftChild->lock);
                splitParent(node, rightChild, insertionPoint, newKey, order, rc)
            }
        case None =>
            // In this case, leftChild is the root of the tree
            // and we must construct a new root node
            let children = Array.empty(rc, order); 
            let keys = Array.empty(rc, order - 1);
            Array.put(leftChild, 0, children);
            Array.put(rightChild, 1, children);
            Array.put(newKey, 0, keys);
            let newRoot = new BLTNode @ rc {
                keys = keys,
                children = Some(children),
                values = None,
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

    // No locks be careful
    pub def rangeQueryWith(f: k -> v -> Unit \ r0, min: k, max: k, node: BLTNode[k, v, r1]): Unit \ {r0, r1} with ToString[k], ToString[v], Order[k], Order[v] =
        let minLeaf = findLeafUnsafe(min, node);
        let index = binarySearch(min, minLeaf->size, minLeaf->keys);
        if(index < 0) {
            let insertionPoint = toInsertionPoint(index);
            if (insertionPoint <= minLeaf->size)
                traverseRight(f, insertionPoint, max, minLeaf)
                else ()
        } else 
            traverseRight(f, index, max, minLeaf)

    def traverseRight(f: k -> v -> Unit \ r0, index: Int32, max: k, node: BLTNode[k, v, r1]): Unit \ {r0, r1} with ToString[k], ToString[v], Order[k], Order[v] =
        if(index < node->size) {
            let k = Array.get(index, node->keys);
            if(k <= max) {
                MutSet.forEach(v -> f(k, v), Array.get(index, unwrap(node->values)));
                traverseRight(f, index + 1, max, node)
            } else ()
        } else match node->next {
            case Some(next) => traverseRight(f, 0, max, next)
            case None => ()
        }
        
}

mod Fixpoint.BLinkTree {
    import java.lang.System
    use Fixpoint.BLinkTree
    use Fixpoint.BLTNode
    use Fixpoint.Lock

    pub def empty(rc: Region[r], order: Int32): BLinkTree[k, v, r] \ r with Order[k] = 
        if (order <= 2)
            bug!("order of tree must be at least 3")
        else
            let node = new BLTNode @ rc {
                keys = Array.empty(rc, order), 
                children = None,
                values = Some(Array.empty(rc, order)),
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

    pub def getRootUnsafe(tree: BLinkTree[k, v, r]): BLTNode[k, v, r] \ r =  tree->root

    pub def getOrder(tree: BLinkTree[k, v, r]): Int32 = tree->order

    pub def insert(key: k, val: v, tree: BLinkTree[k, v, r]): Unit \ r with ToString[k], ToString[v], Order[k], Order[v] = 
        let getRoot: Unit -> BLTNode[k, v, r] \ r = () -> getRoot(tree);
        let leaf = BLTNode.findLeaf(key, getRoot);
        let newRoot = BLTNode.insertIntoLeaf(leaf, key, val, tree->order, tree->rc);
        match newRoot {
            case Some(root) => 
                Lock.lock(tree->rootLock);
                let oldRoot = tree->root;
                tree->root = root;
                Lock.unlock(tree->rootLock);
                Lock.unlock(BLTNode.lock(oldRoot));
                Lock.unlock(BLTNode.lock(root))
            case None => ()
        }

    pub def isEmpty(tree: BLinkTree[k, v, r]): Bool \ r = match BLTNode.children(tree->root) {
        case Some(_) => false
        case None => BLTNode.isEmpty(tree->root)
    }

    pub def memberOf(key: k, val: v, tree: BLinkTree[k, v, r]): Bool \ r with ToString[k], ToString[v], Order[k], Order[v] = 
        let leaf = BLTNode.findLeafUnsafe(key, tree->root);
        BLTNode.contains(key, val, leaf)

    pub def rangeQueryWith(f: k -> v -> Unit \ ef, min: k, max: k, tree: BLinkTree[k, v, r]): Unit \ {r, ef} with Order[k], Order[v], ToString[v], ToString[k] = 
        BLTNode.rangeQueryWith(f, min, max, tree->root)

    // Locks the root and provides a lock on the root node.
    pub def getRoot(tree: BLinkTree[k, v, r]): BLTNode[k, v, r] \ r = 
        Lock.lock(tree->rootLock);
        let root = tree->root;
        let success = Lock.tryLock(BLTNode.lock(root));
        Lock.unlock(tree->rootLock);
        if(success) 
            root
        else {
            // Wait for the thread that was operating on the root to finish
            Lock.lock(BLTNode.lock(root));
            Lock.unlock(BLTNode.lock(root));
            getRoot(tree)
        }
        
    pub def main3(): Unit \ {IO, NonDet} = region rc {
        println("Hej1");
        let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 8);
        let start = System.nanoTime();
        List.forEach(i -> insert(i, Int32.modulo(Random.runWithIO(Random.randomInt32), 30), tree), List.shuffle(List.range(0, 50)));
        let time = System.nanoTime() - start;
        println("Time: ${time / 1000000i64} ms");
        // List.forEach(i -> insert(i, Int32.modulo(Random.runWithIO(Random.randomInt32), 30), tree), List.shuffle(List.range(0, 50)));
        println("Hej2");

        insert(5, 10, tree);
        insert(5, 7, tree);
        insert(6, 8, tree);
        insert(10, 2, tree);
        insert(1, 4, tree);
        println(tree->root);
        println("Hej");
        rangeQueryWith(k -> v -> println("${k}: ${v}"), 0, -2, tree);
        rangeQueryWith(k -> v -> println("${k}: ${v}"), 0, 12, tree);
        rangeQueryWith(k -> v -> println("${k}: ${v}"), 4, 6, tree);
        rangeQueryWith(k -> v -> println("${k}: ${v}"), 5, 12, tree);
        rangeQueryWith(k -> v -> println("${k}: ${v}"), 11, 12, tree);
        rangeQueryWith(k -> v -> println("${k}: ${v}"), 11, 0, tree);
        ()
    }

    pub def main4(): Unit \ IO = region rc {
        let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 5);
        List.forEach(i -> insert(i, i+1, tree), List.range(0, 100));
        // insert(5, 10, tree);
        // insert(6, 11, tree);
        // insert(7, 11, tree);
        println(tree->root);
        // println("");
        ()
    }

    pub def main5(): Unit \ IO = region rc {
        let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 3);
        insert(6, 11, tree);
        insert(5, 10, tree);
        insert(7, 11, tree);
        println(tree->root);
        // println("");
        ()
    }

    pub def main6(): Unit \ IO = region rc {
        let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 3);
        insert(7, 12, tree);
        insert(3, 13, tree);
        insert(6, 11, tree);
        insert(3, 13, tree);
        insert(5, 10, tree);
        insert(8, 13, tree);
        insert(2, 13, tree);
        insert(3, 13, tree);
        insert(4, 13, tree);
        insert(100, 13, tree);
        insert(-23, 13, tree);
        insert(-2, 13, tree);
        insert(-22, 13, tree);
        insert(-24, 13, tree);
        insert(-21, 13, tree);
        insert(-25, 13, tree);
        insert(-21, 13, tree);
        insert(-25, 13, tree);
        insert(-20, 13, tree);
        insert(-26, 13, tree);
        insert(-19, 13, tree);
        insert(-27, 13, tree);
        insert(-18, 13, tree);
        insert(-28, 13, tree);
        insert(-27, 13, tree);
        insert(-29, 13, tree);
        // println(tree->root);
        // unchecked_cast(println("INSERTING -17"));
        insert(-17, 13, tree);
        insert(-30, 13, tree);
        insert(-2, 13, tree);
        insert(-10, 13, tree);
        println(tree->root);
        // println("");
        ()
    }

    pub def main7(): Unit \ IO = region rc{
        let tree = BLinkTree.empty(rc, 5);
        let pairs = List.map(p -> {
            let (x, y) = p;
            (Int32.modulo(x * 1000, 179), Int32.modulo(y * 1003, 109))
        }, List.zip(List.range(1, 79), List.reverse(List.range(1, 79))));
        List.forEach(p -> {
            let (x, y) = p;
            BLinkTree.insert(x, y, tree)
        }, pairs);
        println(tree->root)

}}
