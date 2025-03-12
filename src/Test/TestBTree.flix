mod TestBTree {
    import java.util.concurrent.Helpers
    use Array.sameElements
    use Fixpoint.BLinkTree
    use Fixpoint.BLTNode
    use Fixpoint.Helpers.{unwrap, ptrEqual}

    type alias StandardTree[r: Eff] = BLinkTree[Int32, Int32, r]

    /////////////////////////////////////////////////////////////////////////////
    // Test invariant about the BTree                                          //
    /////////////////////////////////////////////////////////////////////////////
    pub def testTreeInvariant(tree: BLinkTree[k, v, r]): Bool \ r with Order[k], Order[v] = 
        let root = BLinkTree.getRootUnsafe(tree);
        let order = BLinkTree.getOrder(tree);
        let nodeWorks = testNodeInvariant(root, order, true);
        let rootHasNoParent = Option.isEmpty(BLTNode.parent(root));
        nodeWorks and rootHasNoParent

    pub def testNodeInvariant(node: BLTNode[k, v, r], order: Int32, isRightMost: Bool): Bool \ r with Order[k], Order[v] = 
        match BLTNode.children(node) {
        case Some(c) =>
            let size = BLTNode.size(node);
            let keys = toLength(Array.toVector(BLTNode.keys(node)), size - 1);
            let children = toLength(Array.toVector(c), size);
            let keysInOrder = isInOrder(keys);
            let childrenWorks = Vector.forAll(x -> testNodeInvariant(x, order, false), toLength(children, size - 1))
                                and testNodeInvariant(unwrap(Vector.last(children)), order, isRightMost);
            let parentPointerCorrect = Vector.foldLeft(workingSoFar -> cur -> workingSoFar and ptrEqual(node, unwrap(BLTNode.parent(cur))), true, children);
            let nextPointerCorrect = applyPredicate(children, prev -> cur -> ptrEqual(unwrap(BLTNode.next(prev)), cur));
            let lastHasNoNext = not isRightMost or Option.isEmpty(BLTNode.next(unwrap(Vector.last(children))));
            let noLeaves = Option.isEmpty(BLTNode.values(node));
            parentPointerCorrect and nextPointerCorrect and lastHasNoNext and noLeaves and keysInOrder and childrenWorks
        case None => 
            let size = BLTNode.size(node);
            let keys = toLength(Array.toVector(BLTNode.keys(node)), size);
            let leaves = Array.toVector(unwrap(BLTNode.values(node)));
            let keysInOrder = isInOrder(toLength(keys, size));
            let sizeInRange = size <= order and 0 <= size;
            let leavesNonEmpty = Vector.foldLeft(workingSoFar -> cur -> 
                workingSoFar and (MutSet.size(cur) > 0), true, toLength(leaves, size));
            leavesNonEmpty and sizeInRange and keysInOrder
    }

    pub def toLength(v: Vector[v], length: Int32): Vector[v] =
        Vector.slice(start = 0, end = length, v)

    pub def isInOrder(v: Vector[k]): Bool with Order[k] =
        applyPredicate(v, x -> y -> x <= y)

    pub def applyPredicate(v: Vector[k], f: k -> k -> Bool \ r): Bool \ r = 
        let zipped = Vector.map(x -> (x, true), v);
        let reduced =  Vector.reduceLeft(old -> cur -> 
            let (oldNum, oldBool) = old;
            let (curNum, _) = cur;
            (curNum, oldBool and f(oldNum, curNum))
        , zipped);
        match reduced {
            case None => true
            case Some((_, bool)) => bool
        }

    /////////////////////////////////////////////////////////////////////////////
    // empty                                                                   //
    /////////////////////////////////////////////////////////////////////////////
    @test
    pub def empty01(): Bool = region rc {
        let tree: StandardTree[rc] = BLinkTree.empty(rc, 120);
        BLinkTree.isEmpty(tree)
    }

    /////////////////////////////////////////////////////////////////////////////
    // insert                                                                  //
    /////////////////////////////////////////////////////////////////////////////
    @test
    pub def insert01(): Bool = region rc {
        let tree = BLinkTree.empty(rc, 3);
        BLinkTree.insert(4, 2, tree);
        BLinkTree.memberOf(4, 2 ,tree)
    }

    @test
    pub def insert02(): Bool = region rc {
        let tree = BLinkTree.empty(rc, 3);
        BLinkTree.insert(1, 10, tree);
        BLinkTree.insert(2, 11, tree);
        BLinkTree.insert(3, 12, tree);
        BLinkTree.memberOf(1, 10, tree) and
            BLinkTree.memberOf(2, 11, tree) and
            BLinkTree.memberOf(3, 12, tree) and
            testTreeInvariant(tree)
    }

    @test
    pub def insert03(): Bool = region rc {
        let tree = BLinkTree.empty(rc, 3);
        BLinkTree.insert(6, 15, tree);
        BLinkTree.insert(5, 14, tree);
        BLinkTree.insert(4, 13, tree);
        BLinkTree.insert(3, 12, tree);
        BLinkTree.insert(2, 11, tree);
        BLinkTree.insert(1, 10, tree);
        BLinkTree.memberOf(1, 10, tree) and
            BLinkTree.memberOf(2, 11, tree) and
            BLinkTree.memberOf(3, 12, tree) and 
            BLinkTree.memberOf(4, 13, tree) and 
            BLinkTree.memberOf(5, 14, tree) and
            BLinkTree.memberOf(6, 15, tree) and
            testTreeInvariant(tree)
    }
    
    @test
    pub def insert04(): Bool = region rc {
        let tree = BLinkTree.empty(rc, 5);
        let pairs = List.map(p -> {
            let (x, y) = p;
            (Int32.modulo(x * 1000, 179), Int32.modulo(y * 1003, 109))
        }, List.zip(List.range(1, 100), List.reverse(List.range(1, 100))));
        List.forEach(p -> {
            let (x, y) = p;
            BLinkTree.insert(x, y, tree)
        }, pairs);
        List.forAll(p -> {
            let (x, y) = p;
            BLinkTree.memberOf(x, y, tree)
        }, pairs) and testTreeInvariant(tree)
    }
    
    /////////////////////////////////////////////////////////////////////////////
    // rangeQueryWith                                                          //
    /////////////////////////////////////////////////////////////////////////////
    pub def rangeQueryDefaultTree(rc: Region[r]): BLinkTree[Int32, Int32, r] \ r =
        let tree: BLinkTree[Int32, Int32, r] = BLinkTree.empty(rc, 3);
        BLinkTree.insert(0, 10, tree);
        BLinkTree.insert(1, 11, tree);
        BLinkTree.insert(2, 12, tree);
        BLinkTree.insert(3, 13, tree);
        BLinkTree.insert(4, 14, tree);
        BLinkTree.insert(5, 15, tree);
        tree

    pub def rangeQueryMultipleValues(rc: Region[r]): BLinkTree[Int32, Int32, r] \ r =
        let tree = BLinkTree.empty(rc, 3);
        BLinkTree.insert(0, 10, tree);
        BLinkTree.insert(0, 11, tree);
        BLinkTree.insert(0, 12, tree);
        BLinkTree.insert(1, 11, tree);
        BLinkTree.insert(1, 12, tree);
        BLinkTree.insert(2, 13, tree);
        BLinkTree.insert(3, 14, tree);
        tree

    @test
    pub def rangeQueryWith01(): Bool = region rc {
        let tree = rangeQueryDefaultTree(rc);
        let list = MutList.empty(rc);
        let f = k -> _ -> MutList.push(k, list);
        BLinkTree.rangeQueryWith(f, 0, 5, tree);
        let res = Vector#{0, 1, 2, 3, 4, 5};
        MutList.toVector(list) `Vector.equals` res
    }

    @test
    pub def rangeQueryWith02(): Bool = region rc {
        let tree = rangeQueryDefaultTree(rc);
        let list = MutList.empty(rc);
        let f = k -> _ -> MutList.push(k, list);
        BLinkTree.rangeQueryWith(f, -2, 5, tree);
        let res = Vector#{0, 1, 2, 3, 4, 5};
        MutList.toVector(list) `Vector.equals` res
    }

    @test
    pub def rangeQueryWith03(): Bool = region rc {
        let tree = rangeQueryDefaultTree(rc);
        let list = MutList.empty(rc);
        let f = k -> _ -> MutList.push(k, list);
        BLinkTree.rangeQueryWith(f, -2, 7, tree);
        let res = Vector#{0, 1, 2, 3, 4, 5};
        MutList.toVector(list) `Vector.equals` res
    }

    @test
    pub def rangeQueryWith04(): Bool = region rc {
        let tree = rangeQueryDefaultTree(rc);
        let list = MutList.empty(rc);
        let f = k -> _ -> MutList.push(k, list);
        BLinkTree.rangeQueryWith(f, 1, 1, tree);
        let res = Vector#{1};
        MutList.toVector(list) `Vector.equals` res
    }

    @test
    pub def rangeQueryWith05(): Bool = region rc {
        let tree = rangeQueryDefaultTree(rc);
        let list = MutList.empty(rc);
        let f = k -> _ -> MutList.push(k, list);
        BLinkTree.rangeQueryWith(f, 1, 3, tree);
        let res = Vector#{1, 2, 3};
        MutList.toVector(list) `Vector.equals` res
    }

    @test
    pub def rangeQueryWith06(): Bool = region rc {
        let tree = rangeQueryDefaultTree(rc);
        let list = MutList.empty(rc);
        let f = k -> _ -> MutList.push(k, list);
        BLinkTree.rangeQueryWith(f, -2, -2, tree);
        let res = Vector#{ };
        MutList.toVector(list) `Vector.equals` res
    }

    @test
    pub def rangeQueryWith07(): Bool = region rc {
        let tree = rangeQueryDefaultTree(rc);
        let list = MutList.empty(rc);
        let f = k -> _ -> MutList.push(k, list);
        BLinkTree.rangeQueryWith(f, 7, 7, tree);
        let res = Vector#{ };
        MutList.toVector(list) `Vector.equals` res
    }

    @test
    pub def rangeQueryWith08(): Bool = region rc {
        let tree = rangeQueryMultipleValues(rc);
        let list = MutList.empty(rc);
        let f = k -> v -> MutList.push((k, v), list);
        BLinkTree.rangeQueryWith(f, 0, 3, tree);
        let res = Vector#{(0, 10), (0, 11), (0, 12), (1, 11), (1, 12), (2, 13), (3, 14)};
        MutList.toVector(list) `Vector.equals` res
    }
}