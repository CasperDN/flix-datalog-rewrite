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

mod Test.Library.Fixpoint.Phase.JoinOptimizer {
    use Fixpoint.Phase.JoinOptimizer.powerSetOfSize
    
    ///
    /// Returns the powerset of `list`.
    ///
    def powerSet(list: List[a]): List[List[a]] = match list {
        case Nil => Nil :: Nil
        case x :: xs => 
            let ps = powerSet(xs);
            ps ::: List.map(ss -> x :: ss, ps)
    }

    @Test
    def testPowerSetOfSize01(): Bool = {
        let set = 1 :: 2 :: 3 :: 4 :: Nil;
        let res = (1 :: Nil) :: (2 :: Nil) :: (3 :: Nil) :: (4 :: Nil) :: Nil;
        powerSetOfSize(1, set) == res
    }
    
    @Test
    def testPowerSetOfSize02(): Bool = {
        let set = 1 :: 2 :: 3 :: 4 :: Nil;
        let res = 
            (1 :: 2 :: Nil) :: (2 :: 3 :: Nil) :: 
            (3 :: 4 :: Nil) :: (1 :: 3 :: Nil) ::
            (1 :: 4 :: Nil) :: (2 :: 4 :: Nil) :: Nil;
        powerSetOfSize(2, set) == List.sort(res)
    }

    @Test
    def testPowerSetOfSize03(): Bool = {
        let set = 1 :: 2 :: 3 :: 4 :: Nil;
        let res = 
            (1 :: 2 :: 3 :: Nil) :: (1 :: 2 :: 4 :: Nil) :: 
            (1 :: 3 :: 4 :: Nil) :: (2 :: 3 :: 4 :: Nil) :: Nil;
        powerSetOfSize(3, set) == List.sort(res)
    }

    @Test
    def testPowerSetOfSize04(): Bool = {
        let set = 1 :: 2 :: 3 :: 4 :: Nil;
        let res = (1 :: 2 :: 3 :: 4 :: Nil) :: Nil;
        powerSetOfSize(4, set) == res
    }

    @Test
    def testPowerSetOfSize06(): Bool = {
        let k = 17;
        List.range(2,k) |> 
        List.forAll(i -> 
            let set = List.range(0, i);
            let ps1 = powerSet(set) |> List.filter(x -> List.length(x) == i) |> List.sort;
            let ps2 = powerSetOfSize(i, set);
            ps1 == ps2
        )
    }

}