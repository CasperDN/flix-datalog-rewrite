mod MutList {

    pub def rawGet(i: Int32, list: MutList[v, r]): v \ r = Array.get(i, list->values)    

}

instance ToString[Fixpoint.BTree.Node[k, v, r]] with ToString[k], ToString[v] {

    pub def toString(x: Fixpoint.BTree.Node[k, v, r]): String = 
        unchecked_cast(Fixpoint.BTree.Node.toString(x, 0) as _ \ { })

}


mod Fixpoint.BTree {
    type alias Compare[v] = v -> v -> Comparison

    def unwrap(x: Option[a]): a = match x {
        case Some(v) => v
        case None => bug!("Attempted unwrapping None")
    }  

    pub struct BLinkTree[k, v, r] {
        mut root: Node[k, v, r],
        order:    Int32,
        rc:       Region[r]
    }

    pub struct Node[k, v, r] {
        keys:       MutList[k, r], // Acts as keys for internal nodes and values for leaves
        children:   Option[MutList[Node[k, v, r], r]],
        mut parent: Option[Node[k, v, r]],
        mut next:   Option[Node[k, v, r]]
    }     

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
        println(unchecked_cast(binarySearch(6, list, compare) as _ \ IO))
    }    

    pub def sortedInsert(x: v, list: MutList[v, r], compare: Compare[v]): Unit \ r = 
        let index = binarySearch(x, list, compare);
        if (index < 0)
            MutList.insert(x, toInsertionPoint(index), list)
        else bug!("Key should be unique 2")

    // Perform a binary search and return the index of `key` in `list` if it exists.
    // Otherwise, return (-insertionPoint - 1). See Java binary search documentation for arrays.
    pub def binarySearch(key: v, list: MutList[v, r], compare: Compare[v]): Int32 \ r = 
        if (MutList.isEmpty(list)) 
            -1
        else
            def f(l: Int32, r: Int32): Int32 \ r = {
                if (l <= r - 1) {
                    let m = (l + r) / 2;
                    let cur = MutList.rawGet(m, list);
                    match compare(cur, key) {
                        case Comparison.LessThan => f(m + 1, r)
                        case Comparison.GreaterThan => f(l, m)
                        case Comparison.EqualTo => m
                    }
                } else -l-1
            }; 
            f(0, MutList.length(list))

    pub def toInsertionPoint(i: Int32): Int32 = -i-1

    mod Node {
        use Fixpoint.BTree.{Node, Compare, unwrap}
        use Fixpoint.BTree.{binarySearch, sortedInsert, toInsertionPoint}
        pub def parent(node: Node[k, v, r]): Option[Node[k, v, r]] \ r = node->parent
        pub def next(node: Node[k, v, r]): Option[Node[k, v, r]] \ r = node->next
        pub def children(node: Node[k, v, r]): Option[MutList[Node[k, v, r], r]]  = node->children
        pub def keys(node: Node[k, v, r]): MutList[k, r] = node->keys

        pub def toString(node: Node[k, v, r], indent: Int32): String \ r with ToString[k], ToString[v] = 
            let indentString = String.repeat(indent, " ");
            let keysString = MutList.toString(node->keys);
            let extra = match node->children {
                case Some(children) =>              
                    let childrenString = MutList.foldLeft(a -> x -> "${a}${toString(x, indent+2)}", "", children);
                    "${childrenString}"
                case None => ""
            };
            "${indentString}${keysString}\n${extra}"

        // Traverse the tree until a leaf is reached
        pub def traverse(node: Node[k, v, r], val: k, compare: Compare[k]): Node[k, v, r] \ r = match node->children {
            case Some(children) =>
                let index = binarySearch(val, node->keys, compare);
                let childToVisit = if (index < 0) {
                    MutList.rawGet(toInsertionPoint(index), children)
                } else 
                    MutList.rawGet(index + 1, children);
                traverse(childToVisit, val, compare)
            case None => node
        }

        // Insert a value into a leaf, potentially causing a split and returning a new root
        pub def insertIntoLeaf(node: Node[k, v, r], val: k, compare: Compare[k], order: Int32, rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v] = 
            let length = MutList.length(node->keys);
            if (length + 1 >= order) 
                splitLeaf(node, val, compare, order, rc)
            else {
                sortedInsert(val, node->keys, compare);
                None
            }

        // Split a leaf and push the middle key into the parent, potentially causing the parent to split and return a new root
        def splitLeaf(leftLeaf: Node[k, v, r], val: k, compare: Compare[k], order: Int32, rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v] = 
            let values = leftLeaf->keys;
            sortedInsert(val, values, compare);
            let arr = MutList.toArray(rc, values);
            // TODO: Insert actual v values

            let rightArr = Array.copyOfRange(rc, order / 2, MutList.length(values), arr);
            unchecked_cast(println("Before truncate: ${MutList.toVector(values)}") as _ \ r);
            MutList.truncate(order / 2, values); 
            let rightList = Array.toMutList(rc, rightArr);
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

        def fixParent(parent: Node[k, v, r], compare: Compare[k], order: Int32, rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v] =
            let children = unwrap(parent->children);
            if (MutList.length(children) <= order) None
            else
            let middle = (order + 1) / 2;
            let childrenArr = MutList.toArray(rc, children);
            unchecked_cast(println("middle: ${middle}") as _ \ r);
            unchecked_cast(println("lenchildren: ${MutList.length(children)}") as _ \ r);
            let rightChildrenArr = Array.copyOfRange(rc, middle, MutList.length(children), childrenArr);
            MutList.truncate(middle, children);
            let rightChildren = Array.toMutList(rc, rightChildrenArr);
            let keysArr = MutList.toArray(rc, parent->keys);
            // We want to exclude the middle key so + 1
            let rightKeysArr = Array.copyOfRange(rc, middle, MutList.length(parent->keys), keysArr);
            MutList.truncate(middle - 1, parent->keys);
            let rightKeys = Array.toMutList(rc, rightKeysArr);
            let rightNode = new Node @ rc {
                keys = rightKeys,
                children = Some(rightChildren),
                parent = parent->parent,
                next = parent->next
            };
            parent->next = Some(rightNode);
            MutList.forEach(child -> child->parent = Some(rightNode), rightChildren);
            pushKeyToParent(parent->parent, MutList.rawGet(0, rightNode->keys), parent, rightNode, compare, order, rc)
    
        def pushKeyToParent(parent: Option[Node[k, v, r]], 
                          newKey: k, 
                          leftChild: Node[k, v, r],
                          rightChild: Node[k, v, r],
                          compare: Compare[k], 
                          order: Int32, 
                          rc: Region[r]): Option[Node[k, v, r]] \ r with ToString[k], ToString[v] = match parent {
            case Some(node) => 
                let children = unwrap(node->children);
                unchecked_cast(println("leftKeys: ${MutList.toVector(leftChild->keys)}") as _ \ r);
                unchecked_cast(println("rightKeys: ${MutList.toVector(rightChild->keys)}") as _ \ r);
                let index = binarySearch(newKey, node->keys, compare);
                if (index < 0) {
                    let insertionPoint = toInsertionPoint(index);
                    MutList.insert(newKey, insertionPoint, node->keys);
                    MutList.insert(rightChild, insertionPoint + 1, children);
                    None
                } else bug!("Key should be unique");
                fixParent(node, compare, order, rc)
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
        use Fixpoint.BTree.{Node, Compare, unwrap}
        // use Fixpoint.MutList.binarySearch

        pub def empty(rc: Region[r], order: Int32): BLinkTree[k, v, r] \ r = 
            if (order <= 2) 
                bug!("order of tree must be at least 3")
            else
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
            let tree: BLinkTree[Int32, Int32, rc] = empty(rc, 4);
            List.forEach(i -> insert(tree, i, compare), List.reverse(List.range(0, 30)));
            println(tree->root)
        }       

        pub def insert(tree: BLinkTree[k, v, r], val: k, compare: Compare[k]): Unit \ r with ToString[k], ToString[v] = 
            let leaf = Node.traverse(tree->root, val, compare);
            let newRoot = Node.insertIntoLeaf(leaf, val, compare, tree->order, tree->rc);
            match newRoot {
                case Some(root) => tree->root = root
                case None => ()
            }

    }

}