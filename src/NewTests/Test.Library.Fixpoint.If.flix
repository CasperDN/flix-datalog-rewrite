/*
 * Copyright 2025 Casper Dalgaard Nielsen
 *                Adam Yasser Tallouzi
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

mod Test.Exp.Fixpoint.If {
    /////////////////////////////////////////////////////////////////////////////
    // Test if-guard with 0 parameters                                         //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    def testIfGuardZero01(): Bool = {
        let f = inject Vector.range(0, 10) into A/1;
        let r = #{
            Empty(x) :- A(x), if(false).
        };
        Vector.isEmpty(query f, r select x from Empty(x))
    }

    @Test
    def testIfGuardZero02(): Bool = {
        let tuples = Vector.range(0, 10);
        let f = inject tuples into A/1;
        let r = #{
            Empty(x) :- A(x), if(true).
        };
        Vector.sort(query f, r select x from Empty(x)) == tuples
    }

    /////////////////////////////////////////////////////////////////////////////
    // Test if-guard with 1 parameter                                          //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    def testIfGuardOne01(): Bool = {
        let nat = Vector.range(0, 100);
        let f = inject nat into Nat/1;
        let even = Vector.filter(x -> Int32.modulo(x, 2) == 0, nat);
        let r = #{
            Even(x) :- Nat(x), if(Int32.modulo(x, 2) == 0).
        };
        Vector.sort(query f, r select x from Even(x)) == even
    }

    @Test
    def testIfGuardOne02(): Bool = {
        let nat = Vector.range(0, 100);
        let f = inject nat into Nat/1;
        let odd = Vector.filter(x -> Int32.modulo(x, 2) != 0, nat);
        let r = #{
            Odd(x) :- Nat(x), if(Int32.modulo(x, 2) != 0).
        };
        Vector.sort(query f, r select x from Odd(x)) == odd
    }

    @Test
    def testIfGuardOne03(): Bool = {
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
    pub def testIfGuardOne04(): Bool = {
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

    /////////////////////////////////////////////////////////////////////////////
    // Test if-guard with 2 parameters                                         //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    def testIfGuardTwo01(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x + 1));
        let f = inject tuples into A/2;
        let r = #{
            R(x, y) :- A(x, y), if(x + 1 == y).
        };
        Vector.sort(query f, r select (x, y) from R(x, y)) == tuples
    }

    @Test
    def testIfGuardTwo02(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x + 1));
        let f = inject tuples into A/2;
        let r = #{
            R(x, y) :- A(x, y), if(x + 1 == x + 1).
        };
        Vector.sort(query f, r select (x, y) from R(x, y)) == tuples
    }

    /////////////////////////////////////////////////////////////////////////////
    // Test if-guard with 3 parameters                                         //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    def testIfGuardThree01(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x, 2 * x));
        let f = inject tuples into A/3;
        let r = #{
            R(x, y, z) :- A(x, y, z), if(x + y == 2 * x).
        };
        Vector.sort(query f, r select (x, y, z) from R(x, y, z)) == tuples
    }
    
    @Test
    def testIfGuardThree02(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x, 2 * x));
        let f = inject tuples into A/3;
        let r = #{
            R(x, y, z) :- A(x, y, z), if(x + y == z).
        };
        Vector.sort(query f, r select (x, y, z) from R(x, y, z)) == tuples
    }

    @Test
    def testIfGuardThree03(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x, 2 * x));
        let f = inject tuples into A/3;
        let r = #{
            R(x, y, z) :- A(x, y, z), if(x + x == x).
        };
        query f, r select (x, y, z) from R(x, y, z) == Vector#{(0, 0, 0)}
    }

    /////////////////////////////////////////////////////////////////////////////
    // Test if-guard with 4 parameters                                         //
    /////////////////////////////////////////////////////////////////////////////
    
    @Test
    def testIfGuardFour01(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, x, x, x + x + x));
        let f = inject tuples into A/4;
        let r = #{
            R(x, y, z, w) :- A(x, y, z, w), if(x + y + z == w).
        };
        Vector.sort(query f, r select (x, y, z, w) from R(x, y, z, w)) == tuples
    }

    @Test
    def testIfGuardFour02(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, 3 * x));
        let f = inject tuples into A/2;
        let r = #{
            R(x, y) :- A(x, y), if(x + x + x == y).
        };
        Vector.sort(query f, r select (x, y) from R(x, y)) == tuples
    }
    
    /////////////////////////////////////////////////////////////////////////////
    // Test if-guard with 5 parameters                                         //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    def testIfGuardFive01(): Bool = {
        let tuples = Vector.range(0, 100) |> Vector.map(x -> (x, 4 * x));
        let f = inject tuples into A/2;
        let r = #{
            R(x, y) :- A(x, y), if(x + x + x + x == y).
        };
        Vector.sort(query f, r select (x, y) from R(x, y)) == tuples
    }

}