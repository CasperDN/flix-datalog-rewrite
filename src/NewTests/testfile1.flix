mod TestFile1 {

    /////////////////////////////////////////////////////////////////////////////
    // Simple tests                                                            //
    /////////////////////////////////////////////////////////////////////////////
    
    def resultForFirst(n: Int32): Vector[(Int32, Int32, Int32, Int32)] = {
        Vector.range(0, n - 2) |> Vector.map(x -> (x, x + 1, x + 2, x + 3))
    }

    def smallN(): Int32 = 10

    @Test
    def test01(): Bool = {
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
    def test02(): Bool = {
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
    def test03(): Bool = {
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
    def test04(): Bool = {
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
    def test05(): Bool = {
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
    def test06(): Bool = {
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
    def test07(): Bool = {
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
    def test08(): Bool = {
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
    def test09(): Bool = {
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
    def test10(): Bool = {
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

    /////////////////////////////////////////////////////////////////////////////
    // Tests with functional predicates                                        //
    /////////////////////////////////////////////////////////////////////////////


    def isPrime(x: Int32): Bool = 
        def loop(i) =
            if (i > x / 2) true 
            else if (Int32.modulo(x, i) == 0) false 
            else loop(i+1);
        if(x < 2) false
        else loop(2)
    
    def primesInRange(b: Int32, e: Int32): Vector[Int32] = 
        Vector.range(b, e) |> Vector.filter(isPrime)


    @Test
    def test11(): Bool = {
        let p = #{
            P(100).
            Primes(x) :- P(y), let x = primesInRange(0, y).
        };
        query p select (x) from Primes(x) |> Vector.sort == Vector#{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
    }

    @Test
    pub def test12(): Bool = {
        let startinPrimes = inject Vector#{2, 3, 5, 7, 11} into PrimesUntil/1;
        let p = #{
            PrimesPlus20(x + 20):- PrimesUntil(x).
            PrimesUntil(x) :- PrimesPlus20(y), let x = primesInRange(0, y).
        };
        query startinPrimes, p select (x) from PrimesUntil(x) |> Vector.sort == Vector#{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887}
    }

    // @Test
    // def test12(): Bool = {
    //     let p = #{
    //         Primes1(x)             :- let x = primesInRange(0, 100).
    //     };
    //     query p select (x) from Primes1(x) |> Vector.sort == Vector#{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97}
    // }

    /////////////////////////////////////////////////////////////////////////////
    // Tests with if-guards                                                    //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    def testGuard01(): Bool = {
        let nat = Vector.range(0, 100);
        let f = inject nat into Nat/1;
        let even = Vector.filter(x -> Int32.modulo(x, 2) == 0, nat);
        let r = #{
            Even(x) :- Nat(x), if(Int32.modulo(x, 2) == 0).
        };
        Vector.sort(query f, r select x from Even(x)) == even
    }

    @Test
    def testGuard02(): Bool = {
        let nat = Vector.range(0, 100);
        let f = inject nat into Nat/1;
        let odd = Vector.filter(x -> Int32.modulo(x, 2) != 0, nat);
        let r = #{
            Odd(x) :- Nat(x), if(Int32.modulo(x, 2) != 0).
        };
        Vector.sort(query f, r select x from Odd(x)) == odd
    }

    @Test
    def testGuard03(): Bool = {
        let nat = Vector.range(0, 100);
        let f = inject nat into Nat/1;
        let even = Vector.filter(x -> Int32.modulo(x, 2) == 0, nat);
        let odd = Vector.filter(x -> Int32.modulo(x, 2) != 0, nat);
        let r = #{
            Even(x) :- Nat(x), if(Int32.modulo(x, 2) == 0).
            Odd(x) :- Nat(x), if(Int32.modulo(x, 2) != 0).
        };
        Vector.sort(query f, r select x from Even(x)) == even and
            Vector.sort(query f, r select x from Odd(x)) == odd
    }

    @Test
    pub def testGuard04(): Bool = {
        let nat = Vector.range(0, 100);
        let f = inject nat into Nat/1;
        let even = Vector.filter(x -> Int32.modulo(x, 2) == 0, nat);
        let odd = Vector.filter(x -> Int32.modulo(x, 2) != 0, nat);
        let r = #{
            Even(x) :- Nat(x), if(Int32.modulo(x, 2) == 0).
            Odd(x) :- Nat(x), if(Int32.modulo(x, 2) != 0).
        };
        let res = even |> Vector.flatMap(e -> odd |> Vector.map(o -> (e, o))) |> Vector.sort;
        Vector.sort(query f, r select (x, y) from Even(x), Odd(y)) == res
    }

    @Test
    def testGuard05(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x + 1));
        let f = inject tuples into A/2;
        let r = #{
            R(x, y) :- A(x, y), if(x + 1 == y).
        };
        Vector.sort(query f, r select (x, y) from R(x, y)) == tuples
    }

    @Test
    def testGuard06(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x, 2 * x));
        let f = inject tuples into A/3;
        let r = #{
            R(x, y, z) :- A(x, y, z), if(x + y == 2 * x).
        };
        Vector.sort(query f, r select (x, y, z) from R(x, y, z)) == tuples
    }
    
    @Test
    def testGuard07(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x, 2 * x));
        let f = inject tuples into A/3;
        let r = #{
            R(x, y, z) :- A(x, y, z), if(x + y == z).
        };
        Vector.sort(query f, r select (x, y, z) from R(x, y, z)) == tuples
    }

}