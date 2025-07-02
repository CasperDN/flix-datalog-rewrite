mod Test.Exp.Fixpoint.Solve.Permutations {

    /////////////////////////////////////////////////////////////////////////////
    // Simple tests                                                            //
    /////////////////////////////////////////////////////////////////////////////
    
    def resultForFirst(n: Int32): Vector[(Int32, Int32, Int32, Int32)] = {
        Vector.range(0, n - 2) |> Vector.map(x -> (x, x + 1, x + 2, x + 3))
    }

    def smallN(): Int32 = 10

    @Test
    def testPermutation01(): Bool = {
        let n = smallN();
        let a_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into A/2;
        let b_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into B/2;
        let c_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into C/2;
        let p = #{
            D(a, b, c, d) :- A(a, b), B(b, c), C(c, d).
        };
        (query a_, b_, c_, p select (a, b, c, d) from D(a, b, c, d)) |> Vector.sort == resultForFirst(n)
    }

    @Test
    def testPermutation02(): Bool = {
        let n = smallN();
        let a_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into A/2;
        let b_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into B/2;
        let c_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into C/2;
        let p = #{
            D(a, b, c, d) :- A(a, b), C(c, d), B(b, c).
        };
        (query a_, b_, c_, p select (a, b, c, d) from D(a, b, c, d)) |> Vector.sort == resultForFirst(n)
    }

    @Test
    def testPermutation03(): Bool = {
        let n = smallN();
        let a_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into A/2;
        let b_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into B/2;
        let c_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into C/2;
        let p = #{
            D(a, b, c, d) :- B(b, c), A(a, b), C(c, d).
        };
        (query a_, b_, c_, p select (a, b, c, d) from D(a, b, c, d)) |> Vector.sort == resultForFirst(n)
    }

    @Test
    def testPermutation04(): Bool = {
        let n = smallN();
        let a_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into A/2;
        let b_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into B/2;
        let c_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into C/2;
        let p = #{
            D(a, b, c, d) :- B(b, c), C(c, d), A(a, b).
        };
        (query a_, b_, c_, p select (a, b, c, d) from D(a, b, c, d)) |> Vector.sort == resultForFirst(n)
    }

    @Test
    def testPermutation05(): Bool = {
        let n = smallN();
        let a_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into A/2;
        let b_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into B/2;
        let c_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into C/2;
        let p = #{
            D(a, b, c, d) :- C(c, d), A(a, b), B(b, c).
        };
        (query a_, b_, c_, p select (a, b, c, d) from D(a, b, c, d)) |> Vector.sort == resultForFirst(n)
    }

    @Test
    def testPermutation06(): Bool = {
        let n = smallN();
        let a_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into A/2;
        let b_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into B/2;
        let c_ = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into C/2;
        let p = #{
            D(a, b, c, d) :- C(c, d), B(b, c), A(a, b).
        };
        (query a_, b_, c_, p select (a, b, c, d) from D(a, b, c, d)) |> Vector.sort == resultForFirst(n)
    }

    /////////////////////////////////////////////////////////////////////////////
    // Tests with negation                                                     //
    /////////////////////////////////////////////////////////////////////////////


    def assertPathExample(n: Int32, solved: #{ ConstPath(Int32, Int32), D(Int32, Int32, Int32, Int32), Edge(Int32, Int32), NoPath(Int32, Int32), Node(Int32), OnlyPathsTo(Int32), Path(Int32, Int32), PathFrom(Int32), ReachLonelyNode(Int32) | s56164132 }): Bool = {
        query solved select (x, y) from Edge(x, y) |> Vector.sort == Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) and
            query solved select (x, y) from Path(x, y) |> Vector.sort == Vector.range(0, n) |> Vector.flatMap(x -> Vector.range(x + 1, n + 1) |> Vector.map(y -> (x, y))) and
            query solved select (x, y) from NoPath(x, y) |> Vector.sort == Vector.range(0, n + 1) |> Vector.flatMap(x -> Vector.range(0, x + 1) |> Vector.map(y -> (x, y))) |> Vector.sort and
            query solved select (x) from PathFrom(x) |> Vector.sort == Vector.range(0, n) and
            query solved select (x) from OnlyPathsTo(x) == Vector#{n} and
            query solved select (x) from ReachLonelyNode(x) |> Vector.sort == Vector.range(0, n)
    }

    def smallPathN(): Int32 = 5 * smallN()

    @Test
    def testPermutationNeg01(): Bool = {
        let n = smallPathN();
        let edge = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into Edge/2;
        let p = #{
            Node(x)             :- Edge(x, _).
            Node(x)             :- Edge(_, x).
            Path(x, y)          :- Edge(x, y).
            Path(x, y)          :- Path(x, z), Path(z, y).
            NoPath(x, y)        :- Node(x), Node(y), not Path(x, y).
            PathFrom(x)         :- Path(x, _).
            OnlyPathsTo(x)      :- Node(x), not PathFrom(x).
            ReachLonelyNode(x)  :- Path(x, y), OnlyPathsTo(y).
        };
        let solved = solve edge, p;
        assertPathExample(n, solved)
    }

    @Test
    def testPermutationNeg02(): Bool = {
        let n = smallPathN();
        let edge = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into Edge/2;
        let p = #{
            Node(x)             :- Edge(x, _).
            Node(x)             :- Edge(_, x).
            Path(x, y)          :- Edge(x, y).
            Path(x, y)          :- Path(z, y), Path(x, z).
            NoPath(x, y)        :- Node(x), Node(y), not Path(x, y).
            PathFrom(x)         :- Path(x, _).
            OnlyPathsTo(x)      :- Node(x), not PathFrom(x).
            ReachLonelyNode(x)  :- Path(x, y), OnlyPathsTo(y).
        };
        let solved = solve edge, p;
        assertPathExample(n, solved)
    }

    @Test
    def testPermutationNeg03(): Bool = {
        let n = smallPathN();
        let edge = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into Edge/2;
        let p = #{
            Node(x)             :- Edge(x, _).
            Node(x)             :- Edge(_, x).
            Path(x, y)          :- Edge(x, y).
            Path(x, y)          :- Path(z, y), Path(x, z).
            NoPath(x, y)        :- Node(y), Node(x), not Path(x, y).
            PathFrom(x)         :- Path(x, _).
            OnlyPathsTo(x)      :- Node(x), not PathFrom(x).
            ReachLonelyNode(x)  :- Path(x, y), OnlyPathsTo(y).
        };
        let solved = solve edge, p;
        assertPathExample(n, solved)
    }

    @Test
    def testPermutationNeg04(): Bool = {
        let n = smallPathN();
        let edge = inject Vector.range(0, n) |> Vector.map(x -> (x, x + 1)) into Edge/2;
        let p = #{
            Node(x)             :- Edge(x, _).
            Node(x)             :- Edge(_, x).
            Path(x, y)          :- Edge(x, y).
            Path(x, y)          :- Path(z, y), Path(x, z).
            NoPath(x, y)        :- Node(y), Node(x), not Path(x, y).
            PathFrom(x)         :- Path(x, _).
            OnlyPathsTo(x)      :- Node(x), not PathFrom(x).
            ReachLonelyNode(x)  :- OnlyPathsTo(y), Path(x, y).
        };
        let solved = solve edge, p;
        assertPathExample(n, solved)
    }   

}