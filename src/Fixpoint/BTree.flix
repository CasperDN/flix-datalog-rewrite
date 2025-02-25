mod Fixpoint.BTree {
    type alias Compare[v] = v -> v -> Comparison

    struct NodeData[v, r] {
        parent: Ref[Node[v, r], r],
        next: Ref[Node[v, r], r],
        mut max: v
    }

    enum Node[v: Type, r: Eff] {
        case Internal(MutList[Ref[Node[v, r], r], r], NodeData[v, r])
        case Leaf(MutList[v, r], NodeData[v, r])
    }

    mod NodeData {
        use Fixpoint.BTree.Node
        pub def getData(node: Node[v, r]): NodeData[v, r] = match node {
            case Node.Internal(_, data) => data
            case Node.Leaf(_, data) => data
        }
        pub def getParent(node: Node[v, r]): Ref[Node[v, r], r] = getData(node)->parent
        pub def getNext(node: Node[v, r]): Ref[Node[v, r], r] = getData(node)->next
        pub def getMax(node: Node[v, r]): v \ r = getData(node)->max

    }

    def unwrap(x: Option[a]): a = match x {
        case Some(v) => v
        case None => bug!("Attempted unwrapping None")
    }   

    pub def getElementAt(i: Int32, list: List[v]): v = 
        def f(i2: Int32, list2: List[v]): v = {
            match list2 {
                case x :: xs => if (i == i2) x else f(i2, xs)  
                case Nil => bug!("Out of bounds 'getElementAt'")
            } 
        };
        f(i, list)

    pub def insert(tree: Node[v, r], val: v, compare: Compare[v], order: Int32): v \ r = match tree {
            case Node.Internal(children, _) =>
                // Split node

                // Otherwise 
                let findGreaterChild = child -> {
                    let max = NodeData.getMax(Ref.get(child)); 
                    compare(val, max) == Comparison.GreaterThan
                };
                let childIndex = match MutList.find(findGreaterChild, children) {
                    case Some(child) => unwrap(List.indexOf(child, children)) // Slow, fix later !!!
                    case None => 1
                };
                insert(List.get(childIndex - 1, children), val, compare, order)
            case Node.Leaf(values, data) => ???
        }

    

}