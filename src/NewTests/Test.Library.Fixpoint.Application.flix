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

mod Test.Library.Fixpoint.Application {

    /////////////////////////////////////////////////////////////////////////////
    // Tests with application of 1 argument                                    //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    def testApplicationOne01(): Bool = {
        let tuples = Vector.range(0, 50);
        let f = inject tuples into P/1;
        let r = #{
            R(x, x + 1) :- P(x).
        };
        let res = tuples |> Vector.map(x -> (x, x + 1));
        query f, r select (x, y) from R(x, y) |> Vector.sort == res
    }

    @Test
    def testApplicationOne02(): Bool = {
        let n = 50;
        let res = Vector.range(0, n + 1);
        let r = #{
            Succ(0).
            Succ(x + 1) :- Succ(x), if(x < n)
        };
        query r select x from Succ(x) |> Vector.sort == res
    }

    @Test
    pub def testApplicationOne03(): Bool = {
        let g = x -> {
            let fizz = if (Int32.modulo(x, 3) == 0) "Fizz" else "";
            let buzz = if (Int32.modulo(x, 5) == 0) "Buzz" else "";
            let out = fizz + buzz;
            if (out == "")
                Int32.toString(x)
            else 
                out
        };
        let tuples = Vector.range(1, 21);
        let f = inject tuples into Nat/1;
        let r = #{
            FizzBuzz(x, g(x)) :- Nat(x).
        };
        let res = Vector#{
            "1", "2", "Fizz", "4", "Buzz", "Fizz", "7", "8", "Fizz", "Buzz",
            "11", "Fizz", "13", "14", "FizzBuzz", "16", "17", "Fizz", "19", "Buzz"
        };
        query f, r select (x, y) from FizzBuzz(x, y) |> 
            Vector.sort |> Vector.unzip |> snd == res
    }
    
    /////////////////////////////////////////////////////////////////////////////
    // Tests with application of 2 arguments                                   //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    def testApplicationTwo01(): Bool = {
        let tuples = Vector.range(0, 50);
        let f = inject tuples into P/1;
        let r = #{
            Q(1).
            R(x, x + y) :- P(x), Q(y).
        };
        let res = tuples |> Vector.map(x -> (x, x + 1));
        query f, r select (x, y) from R(x, y) |> Vector.sort == res
    }

    @Test
    def testApplicationTwo02(): Bool = {
        let n = 20;
        let res = Vector#{0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20};
        let r = #{
            Two(2).
            SuccTwo(0).
            SuccTwo(x + y) :- SuccTwo(x), Two(y), if(x < n)
        };
        query r select x from SuccTwo(x) |> Vector.sort == res
    }

    /////////////////////////////////////////////////////////////////////////////
    // Tests with application of 3 arguments                                   //
    /////////////////////////////////////////////////////////////////////////////

    @Test
    pub def testApplicationThree01(): Bool = {
        let tuples = Vector.range(0, 50);
        let f = inject tuples into P/1;
        let r = #{
            Q(1).
            S(2).
            R(x, x + y + z) :- P(x), Q(y), S(z).
        };
        let res = tuples |> Vector.map(x -> (x, x + 1 + 2));
        query f, r select (x, y) from R(x, y) |> Vector.sort == res
    }

    
}