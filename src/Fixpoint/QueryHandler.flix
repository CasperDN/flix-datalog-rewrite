mod Fixpoint.QueryHandler {
    use Fixpoint.QueryHandler.Index.RBTree
    use Fixpoint.Ast.Ram.BoolExp
    // use Index.RBTree
    // use Fixpoint.Ast.Ram.QueryExp
    use Query.EqConst
    use Query.EqIndex

    // For index i build index all indexes described by the innermost on vector of size i on indexes 
    pub type alias ConstructionInfo = Map[Int64, Vector[(Int32, Vector[Int32])]]

    pub type alias InternalInfo[r: Eff] = Vector[Vector[Index[r]]]

    pub enum Query {
        case EqConst(Int32, Int64) // (i, k) => some_relation[i] == k
        case EqIndex(Int32, Int32) // (i, j) => some_relation[i] == some_relation[j]
    }

    pub def initialize(): Unit = ()


    // Red-Black
    // Linked B-Tree
    // Trie

    enum Index[r: Eff] {
        case RBTree(MutMap[Vector[Int64], Int64, r])
        // case LinkedBTree(TypeOfLinkBTree)
        // case Trie(TypeOfLinkBTree)
    }


    pub def rangeQuery(id: Int64, index: Int32, qry: Vector[Query], func: (Vector[Int64] -> Int64 -> Unit), internalInfo: InternalInfo[r]): Unit \ r =
        match Vector.get(unwrap(Int64.tryToInt32(id)), internalInfo) |> Vector.get(index) {
            case RBTree(map) => MutMap.rangeQueryWith(satisfiesQuery(qry), func, map)
        }

    pub def satisfiesQuery(qry: Vector[Query], rel: Vector[Int64]): Comparison =
        let res = Vector.forAll(q -> match q {
            case EqConst(index, value) => Vector.get(index, rel) == value
            case EqIndex(index1, index2) => Vector.get(index1, rel) == Vector.get(index2, rel)
        }, qry);
        if (res) Comparison.EqualTo
        else Comparison.LessThan
    

    def unwrap(opt: Option[v]): v = match opt {
        case Some(v) => v
        case None => bug!("More than 2^32 predicates used...")
    }

    // def getFirst(tuple: (v, w)): v = match tuple {case (x,_) => x}

}