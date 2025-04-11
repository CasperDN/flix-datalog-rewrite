mod TestBPlusTree {
    use Random.randomInt64
    import java.lang.Object
    import java.util.Objects
    use Array.sameElements
    use BPlusTree.Node
    use Fixpoint.Boxed
    use Fixpoint.Boxed.BoxedInt64

    def listToMap(l: List[(Array[Int64, r], Boxed)]): Map[Vector[Int64], Boxed] =
        List.foldLeft(acc -> p -> let (x, y) = p; Map.insert(unchecked_cast(x as Vector[Int64]), y, acc), Map#{}, l)


    /////////////////////////////////////////////////////////////////////////////
    // Test concurrency                                                        //
    /////////////////////////////////////////////////////////////////////////////

    ///
    /// Calls `f` `callNum` times and returns the and of the result.
    ///
    def repeatN(f: Unit -> Bool \ ef, callNum: Int64): Bool \ ef = 
        def repeatNInternal(callNumInternal: Int64, res: Bool): Bool \ ef = {
            if (callNumInternal <= 0i64) res else {
                // If the call to f is inlined Flix crashes for some reason.
                let f_ = f();
                repeatNInternal(callNumInternal - 1i64, res and f_)
            }
        };
        repeatNInternal(callNum, true)

    def totalInsertNum(): Int64 = 300_000i64

    ///
    /// `gen` and `inserted` are the functions that generate the inserted values.
    /// If `inserted` is Some we check that they have been inserted.
    /// For both `gen` and `inserted` every element of the vector will be called `numInserts` times and, respectively, be inserted or test membership.
    ///
    def concurrencyWithGenerators(
        rc: Region[r], 
        gen: Vector[Unit -> (Array[Int64, r], Boxed) \ ef1], 
        numInserts: Int64, 
        inserted: Option[Vector[Unit -> (Array[Int64, r], Boxed) \ ef2]]
    ): Bool \ ef2 + IO + Random + r =
        let tree: BPlusTree[r]  = BPlusTree.emptyWithOrder(rc, 10, defaultSearch()); // Small order to get more splits.
        let seeds = Vector.map(_ -> Random.randomInt64(), gen);
        let _: Unit = region rc2 {
            Vector.forEach(inputt -> {
                let (f, seed) = inputt;
                // Have to remove the effect ef1 and rc as spawn does not accept them
                spawn unchecked_cast(() -> {
                    Random.runWithSeed(seed, () -> repeatN(() -> {
                        let (x, y) = f();
                        BPlusTree.insert(x, y, tree);
                        true
                    }, numInserts)); ()
                } as Unit -> Unit \ IO)() @ rc2}
            , Vector.zip(gen, seeds))
        };
        BPlusTree.assertTreeInvariant(tree)
         and match inserted {
            case None => true
            case Some(shouldBeIn) =>
            Vector.forAll(inputt -> {
                let (f, seed) = inputt;
                Random.runWithSeed(seed, () -> repeatN(() -> {
                    let (x, _) = f();
                    BPlusTree.memberOf(x, tree)
                }, numInserts))}
            , Vector.zip(shouldBeIn, seeds))
        }

    ///
    /// `gen` and `inserted` are the functions that generate the inserted values.
    /// If `inserted` is Some we check that they have been inserted.
    /// For both `gen` and `inserted` every element of the vector will be called `numInserts` times and, respectively, be inserted or test membership
    ///
    def concurrencyWithGeneratorsAndOccasionalTests(
        rc: Region[r],
        gen: Vector[Unit -> (Array[Int64, r], Boxed) \ ef1], 
        numInserts: Int64, 
        inserted: Vector[Unit -> (Array[Int64, r], Boxed) \ ef2], 
        readEvery: Int64
    ): Bool \ IO + Random + r = {
        let tree: BPlusTree[r]  = BPlusTree.emptyWithOrder(rc, 10, defaultSearch()); // Small order to get more splits.
        let seeds = Vector.map(_ -> Random.randomInt64(), gen);
        let resultVec = Vector.map(_ -> Ref.fresh(rc, false), Vector.range(0, Vector.length(gen)));
        let insertWithSeed = Vector.map(match (seed, insert) -> Random.handleWithSeed(seed, insert), Vector.zip(seeds, inserted));
        let _: Unit = region rc2 {
            Vector.forEach(inputt -> {
                let (((f, seed), insertedFunc), resultRef) = inputt;
                // Have to remove the effect ef1 and rc as spawn does not accept them
                spawn unchecked_cast(() -> {
                    let countRef = Ref.fresh(rc, 0i64);
                    Random.runWithSeed(seed, () -> Ref.put(repeatN(() -> {
                        let (x, y) = f();
                        BPlusTree.insert(x, y, tree);
                        let cur = Ref.get(countRef);
                        if (cur >= readEvery) {
                            let (x_, _) = insertedFunc();
                            Ref.put(0i64, countRef);
                            BPlusTree.memberOf(x_, tree)
                        } else {
                            Ref.put(cur + 1i64, countRef);
                            true
                        }
                    }, numInserts), resultRef))
                } as Unit -> Unit \ IO)() @ rc2
            }, Vector.zip(Vector.zip(Vector.zip(gen, seeds), insertWithSeed), resultVec))
        };
        Vector.forAll(x -> Ref.get(x), resultVec)
        // res
    }

    ///
    /// Run concurrencyWithGenerators with random values as inserts.
    ///
    def concurrencyRandomInserts(numThreads: Int32, totalInserts: Int64): Bool \ IO + Random = region rc{
        let generators = Vector.map(_ -> () -> (randomArray(rc), BoxedInt64(Random.randomInt64())), Vector.range(0, numThreads));
        let insertions = Vector.map(_ -> () -> (randomArray(rc), BoxedInt64(Random.randomInt64())), Vector.range(0, numThreads));
        concurrencyWithGenerators(rc, generators, totalInserts / Int32.toInt64(numThreads), Some(insertions))
    }
    ///
    /// Run concurrencyWithGenerators with random values between 0 (inclusive) and `rangeSize` (exlusive) as inserts.
    ///
    def concurrencyRandomInsertsClamped(numThreads: Int32, totalInserts: Int64, rangeSize: Int64): Bool \ IO + Random = region rc{
        let generators = Vector.map(_ -> () -> (Array.map(rc, x -> Int64.modulo(x, rangeSize), randomArray(rc)), BoxedInt64(Random.randomInt64())), Vector.range(0, numThreads));
        let insertions = Vector.map(_ -> () -> (Array.map(rc, x -> Int64.modulo(x, rangeSize), randomArray(rc)), BoxedInt64(Random.randomInt64())), Vector.range(0, numThreads));
        concurrencyWithGenerators(rc, generators, totalInserts / Int32.toInt64(numThreads), Some(insertions))
    }
    ///
    /// Run concurrencyWithGenerators with [1, 2, ..., `numInserts`] as inserts for all threads.
    ///
    def concurrencyLockStep(numThreads: Int32, totalInserts: Int64): Bool \ IO + Random = region rc {
        let range = Vector.range(0, numThreads);
        let generators = Vector.map(reff -> () -> {let next = Ref.get(reff); Ref.put(next + 1i64, reff); (Array#{next, 0i64, 0i64} @ rc, BoxedInt64(next))}, Vector.map(_ -> Ref.fresh(rc, 0i64), range));
        let insertions = Vector.map(reff -> () -> {let next = Ref.get(reff); Ref.put(next + 1i64, reff); (Array#{next, 0i64, 0i64} @ rc, BoxedInt64(next))}, Vector.map(_ -> Ref.fresh(rc, 0i64), range));
        concurrencyWithGenerators(rc, generators, totalInserts / Int32.toInt64(numThreads), Some(insertions))
    }

        ///
    /// Run concurrencyWithGeneratorsAndOccasionalTests with random values as inserts.
    ///
    def concurrencyRandomInsertsIntermittentMemberOf(numThreads: Int32, totalInserts: Int64, readEvery: Int64): Bool \ IO + Random = region rc {
        let generators = Vector.map(_ -> () -> (randomArray(rc), BoxedInt64(Random.randomInt64())), Vector.range(0, numThreads));
        let insertions = Vector.map(_ -> () -> (randomArray(rc), BoxedInt64(Random.randomInt64())), Vector.range(0, numThreads));
        concurrencyWithGeneratorsAndOccasionalTests(rc, generators, totalInserts / Int32.toInt64(numThreads), insertions, readEvery)
    }
    
    ///
    /// Run concurrencyWithGeneratorsAndOccasionalTests with random values between 0 (inclusive) and `rangeSize` (exlusive) as inserts.
    ///
    def concurrencyRandomInsertsClampedIntermittentMemberOf(numThreads: Int32, totalInserts: Int64, rangeSize: Int64, readEvery: Int64): Bool \ IO + Random = region rc {
        let generators = Vector.map(_ -> () -> (Array.map(rc, x -> Int64.modulo(x, rangeSize), randomArray(rc)), BoxedInt64(Random.randomInt64())), Vector.range(0, numThreads));
        let insertions = Vector.map(_ -> () -> (Array.map(rc, x -> Int64.modulo(x, rangeSize), randomArray(rc)), BoxedInt64(Random.randomInt64())), Vector.range(0, numThreads));
        concurrencyWithGeneratorsAndOccasionalTests(rc, generators, totalInserts / Int32.toInt64(numThreads), insertions, readEvery)
    }

    ///
    /// Run concurrencyWithGeneratorsAndOccasionalTests with [1, 2, ..., `numInserts`] as inserts for all threads.
    ///
    def concurrencyLockStepIntermittentMemberOf(numThreads: Int32, totalInserts: Int64, readEvery: Int64): Bool \ IO + Random = region rc {
        let range = Vector.range(0, numThreads);
        let generators = Vector.map(reff -> () -> {let next = Ref.get(reff); Ref.put(next + 1i64, reff); (Array#{next, 0i64, 0i64} @ rc, BoxedInt64(next))}, Vector.map(_ -> Ref.fresh(rc, 0i64), range));
        let insertions = Vector.map(reff -> () -> {let next = Ref.get(reff); Ref.put(next + 1i64, reff); (Array#{next, 0i64, 0i64} @ rc, BoxedInt64(next))}, Vector.map(_ -> Ref.fresh(rc, 0i64), range));
        concurrencyWithGeneratorsAndOccasionalTests(rc, generators, totalInserts / Int32.toInt64(numThreads), insertions, readEvery)
    }



    // Large concurrent insertion test-cases
    @test
    def concurrency01(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInserts(10, totalInsertNum()))

    @test
    def concurrency02(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInserts(20, totalInsertNum()))

    @test
    def concurrency03(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInserts(30, totalInsertNum()))

    @test
    def concurrency04(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInsertsClamped(10, totalInsertNum(), 10_000i64))

    @test
    def concurrency05(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInsertsClamped(30, totalInsertNum(), 10_000i64))

    @test
    def concurrency06(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInsertsClamped(20, totalInsertNum(), 10_000i64))

    @test
    def concurrency07(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInsertsClamped(40, totalInsertNum(), 100_000i64))

    @test
    def concurrency08(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyLockStep(10, totalInsertNum()))

    @test
    def concurrency09(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyLockStep(30, totalInsertNum()))

    @test
    def concurrency10(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInsertsIntermittentMemberOf(10, totalInsertNum(), 10i64))

    @test
    def concurrency11(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInsertsIntermittentMemberOf(20, totalInsertNum(), 10i64))

    @test
    def concurrency12(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInsertsIntermittentMemberOf(30, totalInsertNum(), 10i64))

    @test
    def concurrency13(): Bool \ IO + NonDet =
        Random.runWithIO(() -> concurrencyRandomInsertsClampedIntermittentMemberOf(10, totalInsertNum(), 10_000i64, 10i64))

    @test
    def concurrency14(): Bool \ IO + NonDet = 
        Random.runWithIO(() -> concurrencyRandomInsertsClampedIntermittentMemberOf(30, totalInsertNum(), 10_000i64, 10i64))

    @test
    def concurrency15(): Bool \ IO + NonDet = 
        Random.runWithIO(() -> concurrencyRandomInsertsClampedIntermittentMemberOf(20, totalInsertNum(), 10_000i64, 10i64))

    @test
    def concurrency16(): Bool \ IO + NonDet = 
        Random.runWithIO(() -> concurrencyRandomInsertsClampedIntermittentMemberOf(40, totalInsertNum(), 100_000i64, 10i64))

    @test
    def concurrency17(): Bool \ IO + NonDet = 
        Random.runWithIO(() -> concurrencyLockStepIntermittentMemberOf(10, totalInsertNum(), 10i64))

    @test
    def concurrency18(): Bool \ IO + NonDet = 
        Random.runWithIO(() -> concurrencyLockStepIntermittentMemberOf(30, totalInsertNum(), 10i64))

    /////////////////////////////////////////////////////////////////////////////
    // containsPair                                                            //
    /////////////////////////////////////////////////////////////////////////////

    def defaultSearch(): Vector[Int32] = Vector#{0,1,2}

    @test
    def containsPair01(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        not BPlusTree.containsPair(Array#{0i64,1i64,2i64} @ rc, BoxedInt64(0i64), tree) and
            not BPlusTree.containsPair(Array#{2i64,0i64,1i64} @ rc, BoxedInt64(1i64), tree) and
            not BPlusTree.containsPair(Array#{1i64,2i64,0i64} @ rc, BoxedInt64(0i64), tree)
    }
    @test
    def containsPair02(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{5i64,2i64,9i64} @ rc, BoxedInt64(2i64), tree);
        BPlusTree.containsPair(Array#{5i64,2i64,9i64} @ rc, BoxedInt64(2i64), tree) and
            not BPlusTree.containsPair(Array#{9i64,5i64,2i64} @ rc, BoxedInt64(1i64), tree) and
            not BPlusTree.containsPair(Array#{5i64,9i64,2i64} @ rc, BoxedInt64(3i64), tree) and
            not BPlusTree.containsPair(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(3i64), tree)
    }

    /////////////////////////////////////////////////////////////////////////////
    // containsPairThreadUnsafe                                                //
    /////////////////////////////////////////////////////////////////////////////
    @test
    def containsPairUnsafe01(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{5i64,2i64,9i64} @ rc, BoxedInt64(2i64), tree);
        BPlusTree.containsPairThreadUnsafe(Array#{5i64,2i64,9i64} @ rc, BoxedInt64(2i64), tree) and
            not BPlusTree.containsPairThreadUnsafe(Array#{9i64,5i64,2i64} @ rc, BoxedInt64(1i64), tree) and
            not BPlusTree.containsPairThreadUnsafe(Array#{5i64,9i64,2i64} @ rc, BoxedInt64(3i64), tree) and
            not BPlusTree.containsPairThreadUnsafe(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(3i64), tree)
    }
    @test
    def containsPairUnsafe02(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{1i64, 0i64, 0i64} @ rc, BoxedInt64(2i64), tree);
        BPlusTree.containsPairThreadUnsafe(Array#{1i64, 0i64, 0i64} @ rc, BoxedInt64(2i64), tree) and
            not BPlusTree.containsPairThreadUnsafe(Array#{2i64, 0i64, 0i64} @ rc, BoxedInt64(1i64), tree) and
            not BPlusTree.containsPairThreadUnsafe(Array#{1i64, 0i64, 0i64} @ rc, BoxedInt64(3i64), tree)
    }

    /////////////////////////////////////////////////////////////////////////////
    // isEmpty                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def isEmpty01(): Bool = region rc {
        let tree: BPlusTree[rc] = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.isEmpty(tree)
    }

    @test
    def isEmpty02(): Bool = region rc {
        let tree: BPlusTree[rc] = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(2i64), tree);
        not BPlusTree.isEmpty(tree)
    }

    @test
    def isEmpty03(): Bool = region rc {
        let tree: BPlusTree[rc] = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        let empty0 = BPlusTree.isEmpty(tree);
        BPlusTree.insert(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(2i64), tree);
        let empty1 = BPlusTree.isEmpty(tree);
        BPlusTree.insert(Array#{1i64,2i64,3i64} @ rc, BoxedInt64(3i64), tree);
        let empty2 = BPlusTree.isEmpty(tree);
        BPlusTree.insert(Array#{3i64,2i64,1i64} @ rc, BoxedInt64(4i64), tree);
        let empty3 = BPlusTree.isEmpty(tree);
        BPlusTree.insert(Array#{1i64,2i64,1i64} @ rc, BoxedInt64(5i64), tree);
        let empty4 = BPlusTree.isEmpty(tree);
        empty0 and not empty1 and not empty2 and not empty3 and not empty4
    }

    /////////////////////////////////////////////////////////////////////////////
    // isEmptyThreadUnsafe                                                     //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def isEmptyThreadUnsafe01(): Bool = region rc {
        let tree: BPlusTree[rc] = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.isEmptyThreadUnsafe(tree)
    }

    @test
    def isEmptyThreadUnsafe02(): Bool = region rc {
        let tree: BPlusTree[rc] = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(2i64), tree);
        not BPlusTree.isEmptyThreadUnsafe(tree)
    }

    @test
    def isEmptyThreadUnsafe03(): Bool = region rc {
        let tree: BPlusTree[rc] = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        let empty0 = BPlusTree.isEmptyThreadUnsafe(tree);
        BPlusTree.insert(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(2i64), tree);
        let empty1 = BPlusTree.isEmptyThreadUnsafe(tree);
        BPlusTree.insert(Array#{1i64,2i64,3i64} @ rc, BoxedInt64(3i64), tree);
        let empty2 = BPlusTree.isEmptyThreadUnsafe(tree);
        BPlusTree.insert(Array#{3i64,2i64,1i64} @ rc, BoxedInt64(4i64), tree);
        let empty3 = BPlusTree.isEmptyThreadUnsafe(tree);
        BPlusTree.insert(Array#{2i64,6i64,3i64} @ rc, BoxedInt64(5i64), tree);
        let empty4 = BPlusTree.isEmptyThreadUnsafe(tree);
        empty0 and not empty1 and not empty2 and not empty3 and not empty4
    }

    /////////////////////////////////////////////////////////////////////////////
    // insert                                                                  //
    /////////////////////////////////////////////////////////////////////////////

    def randomArray(rc: Region[r]): Array[Int64, r] \ r + Random = 
        Array#{Random.randomInt64(), Random.randomInt64(), Random.randomInt64()} @ rc


    // def getRandomListOfPairs(n: Int32): List[(Int32, Int32)] \ Random =
    //     List.map(_ -> (Random.randomInt32(), Random.randomInt32()), List.range(0, n))

    @test
    def insert01(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(2i64), tree);
        BPlusTree.containsPair(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(2i64) ,tree) and BPlusTree.assertTreeInvariant(tree)
    }

    @test
    def insert02(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(10i64), tree);
        BPlusTree.insert(Array#{1i64,2i64,3i64} @ rc, BoxedInt64(11i64), tree);
        BPlusTree.insert(Array#{2i64, 9i64, 1i64} @ rc, BoxedInt64(12i64), tree);
        BPlusTree.containsPair(Array#{2i64,5i64,9i64} @ rc, BoxedInt64(10i64), tree) and
            BPlusTree.containsPair(Array#{1i64,2i64,3i64} @ rc, BoxedInt64(11i64), tree) and
            BPlusTree.containsPair(Array#{2i64, 9i64, 1i64} @ rc, BoxedInt64(12i64), tree) and
            BPlusTree.assertTreeInvariant(tree)
    }

    @test
    def insert04(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 5, defaultSearch());
        let arrPairs = List.zip3(List.range(1, 10_000), List.range(10_000, 20_000), List.range(10_000, 30_000));
        let pairs = 
            List.zip(arrPairs, List.reverse(List.range(1, 10_000))) |> 
            List.map(match (p1, w) -> 
                let (x,y,z) = p1;
                ((Int32.toInt64(x), Int32.toInt64(y), Int32.toInt64(z)), Int32.toInt64(w))
            ) |>
            List.map(p -> {
                let (p1, w) = p;
                let (x,y,z) = p1;
                (Array#{
                    Int64.modulo(x * 1000i64, 179i64),
                    Int64.modulo(y * 1000i64, 179i64),
                    Int64.modulo(z * 1000i64, 179i64)
                } @ rc, BoxedInt64(Int64.modulo(w * 1003i64, 109i64)))
            });
            List.forEach(p -> {
                let (x, y) = p;
                BPlusTree.insert(x, y, tree)
            }, pairs);
        Map.forAll(x -> y -> {
            BPlusTree.containsPair(unchecked_cast(x as Array[Int64, rc]), y, tree)
        }, listToMap(pairs)) and BPlusTree.assertTreeInvariant(tree)
    }

    @test
    def insert05(): Bool = region rc {
        List.forAll(order -> {
            let tree = BPlusTree.emptyWithOrder(rc, order, defaultSearch());
            let arrPairs = List.zip3(List.range(1, 10_000), List.range(10_000, 20_000), List.range(10_000, 30_000));
        let pairs = 
            List.zip(arrPairs, List.reverse(List.range(1, 10_000))) |> 
            List.map(match (p1, w) -> 
                let (x,y,z) = p1;
                ((Int32.toInt64(x), Int32.toInt64(y), Int32.toInt64(z)), Int32.toInt64(w))
            ) |>
            List.map(p -> {
                let (p1, w) = p;
                let (x,y,z) = p1;
                (Array#{
                    Int64.modulo(x * 1000i64, 179i64),
                    Int64.modulo(y * 1000i64, 179i64),
                    Int64.modulo(z * 1000i64, 179i64)
                } @ rc, BoxedInt64(Int64.modulo(w * 1003i64, 109i64)))
            });
            List.forEach(p -> {
                let (x, y) = p;
                BPlusTree.insert(x, y, tree)
            }, pairs);
            Map.forAll((x, y) -> {
                BPlusTree.containsPair(unchecked_cast(x as Array[Int64, rc]), y, tree)
            }, listToMap(pairs)) and BPlusTree.assertTreeInvariant(tree)
        }, List.range(3, 10))
    }

    /////////////////////////////////////////////////////////////////////////////
    // memberOf                                                                //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def memberOf01(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{2i64, 0i64, 0i64} @ rc, BoxedInt64(3i64), tree);
        BPlusTree.memberOf(Array#{2i64, 0i64, 0i64} @ rc, tree)
    }


    @test
    def memberOf02(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        not BPlusTree.memberOf(Array#{0i64, 0i64, 0i64} @ rc, tree) and
            not BPlusTree.memberOf(Array#{1i64, 0i64, 0i64} @ rc, tree) and
            not BPlusTree.memberOf(Array#{-1i64, 0i64, 0i64} @ rc, tree)
    }

    @test
    def memberOf03(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{1i64, 0i64, 0i64} @ rc, BoxedInt64(2i64), tree);
        BPlusTree.memberOf(Array#{1i64, 0i64, 0i64} @ rc, tree) and
            not BPlusTree.memberOf(Array#{2i64, 0i64, 0i64}@ rc, tree) and
            not BPlusTree.memberOf(Array#{3i64, 0i64, 0i64}@ rc, tree)
    }

    /////////////////////////////////////////////////////////////////////////////
    // memberOfThreadUnsafe                                                          //
    /////////////////////////////////////////////////////////////////////////////

    @test
    def memberOfUnsafe01(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{2i64, 0i64, 0i64} @ rc, BoxedInt64(3i64), tree);
        BPlusTree.memberOfThreadUnsafe(Array#{2i64, 0i64, 0i64} @ rc, tree)
    }

    @test
    def memberOfUnsafe02(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        not BPlusTree.memberOfThreadUnsafe(Array#{0i64, 0i64, 0i64} @ rc, tree) and
            not BPlusTree.memberOfThreadUnsafe(Array#{1i64, 0i64, 0i64} @ rc, tree) and
            not BPlusTree.memberOfThreadUnsafe(Array#{-1i64, 0i64, 0i64} @ rc, tree)
    }

    @test
    def memberOfUnsafe03(): Bool = region rc {
        let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
        BPlusTree.insert(Array#{1i64, 0i64, 0i64} @ rc, BoxedInt64(2i64), tree);
        BPlusTree.memberOfThreadUnsafe(Array#{1i64, 0i64, 0i64} @ rc, tree) and
            not BPlusTree.memberOfThreadUnsafe(Array#{2i64, 0i64, 0i64} @ rc, tree) and
            not BPlusTree.memberOfThreadUnsafe(Array#{0i64, 0i64, 0i64} @ rc, tree)
    }

    /////////////////////////////////////////////////////////////////////////////
    // rangeQueryWith                                                          //
    /////////////////////////////////////////////////////////////////////////////

    // def rangeQueryDefaultTree(rc: Region[r]): BPlusTree[r] \ r =
    //     let tree: BPlusTree[r] = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
    //     BPlusTree.insert(Array#{0i64, 0i64, 0i64} @ rc, 10i64, tree);
    //     BPlusTree.insert(Array#{1i64, 0i64, 0i64} @ rc, 11i64, tree);
    //     BPlusTree.insert(Array#{2i64, 0i64, 0i64} @ rc, 12i64, tree);
    //     BPlusTree.insert(Array#{3i64, 0i64, 0i64} @ rc, 13i64, tree);
    //     BPlusTree.insert(Array#{4i64, 0i64, 0i64} @ rc, 14i64, tree);
    //     BPlusTree.insert(Array#{5i64, 0i64, 0i64} @ rc, 15i64, tree);
    //     tree

    // def rangeQueryMultipleValues(rc: Region[r]): BPlusTree[r] \ r =
    //     let tree = BPlusTree.emptyWithOrder(rc, 3, defaultSearch());
    //     BPlusTree.insert(Array#{0i64, 1i64, 2i64} @ rc, 10i64, tree);
    //     BPlusTree.insert(Array#{0i64, 1i64, 2i64} @ rc, 11i64, tree);
    //     BPlusTree.insert(Array#{0i64, 1i64, 2i64} @ rc, 12i64, tree);
    //     BPlusTree.insert(Array#{1i64, 1i64, 2i64} @ rc, 11i64, tree);
    //     BPlusTree.insert(Array#{1i64, 1i64, 2i64} @ rc, 12i64, tree);
    //     BPlusTree.insert(Array#{2i64, 1i64, 2i64} @ rc, 13i64, tree);
    //     BPlusTree.insert(Array#{3i64, 1i64, 2i64} @ rc, 14i64, tree);
    //     tree

    // @test
    // def rangeQueryWith01(): Bool = region rc {
    //     let tree = rangeQueryDefaultTree(rc);
    //     let list = MutList.emptyWithOrder(rc);
    //     let f = k -> _ -> MutList.push(k, list);
    //     BPlusTree.rangeQueryWith(f, 0, 5, tree);
    //     let res = Vector#{0, 1, 2, 3, 4, 5};
    //     Vector.forAll(Array.compare, Vector.zip(MutList.toVector(list), res))
    //     // MutList.toVector(list) `Vector.equals` res
    // }

    // @test
    // def rangeQueryWith02(): Bool = region rc {
    //     let tree = rangeQueryDefaultTree(rc);
    //     let list = MutList.emptyWithOrder(rc);
    //     let f = k -> _ -> MutList.push(k, list);
    //     BPlusTree.rangeQueryWith(f, -2, 5, tree);
    //     let res = Vector#{0, 1, 2, 3, 4, 5};
    //     Vector.forAll(Array.compare, Vector.zip(MutList.toVector(list), res))
    //     // MutList.toVector(list) `Vector.equals` res
    // }

    // @test
    // def rangeQueryWith03(): Bool = region rc {
    //     let tree = rangeQueryDefaultTree(rc);
    //     let list = MutList.emptyWithOrder(rc);
    //     let f = k -> _ -> MutList.push(k, list);
    //     BPlusTree.rangeQueryWith(f, -2, 7, tree);
    //     let res = Vector#{0, 1, 2, 3, 4, 5};
    //     Vector.forAll(Array.compare, Vector.zip(MutList.toVector(list), res))
    //     // MutList.toVector(list) `Vector.equals` res
    // }

    // @test
    // def rangeQueryWith04(): Bool = region rc {
    //     let tree = rangeQueryDefaultTree(rc);
    //     let list = MutList.emptyWithOrder(rc);
    //     let f = k -> _ -> MutList.push(k, list);
    //     BPlusTree.rangeQueryWith(f, 1, 1, tree);
    //     let res = Vector#{1};
    //     Vector.forAll(Array.compare, Vector.zip(MutList.toVector(list), res))
    //     // MutList.toVector(list) `Vector.equals` res
    // }

    // @test
    // def rangeQueryWith05(): Bool = region rc {
    //     let tree = rangeQueryDefaultTree(rc);
    //     let list = MutList.emptyWithOrder(rc);
    //     let f = k -> _ -> MutList.push(k, list);
    //     BPlusTree.rangeQueryWith(f, 1, 3, tree);
    //     let res = Vector#{1, 2, 3};
    //     Vector.forAll(Array.compare, Vector.zip(MutList.toVector(list), res))
    //     // MutList.toVector(list) `Vector.equals` res
    // }

    // @test
    // def rangeQueryWith06(): Bool = region rc {
    //     let tree = rangeQueryDefaultTree(rc);
    //     let list = MutList.emptyWithOrder(rc);
    //     let f = k -> _ -> MutList.push(k, list);
    //     BPlusTree.rangeQueryWith(f, -2, -2, tree);
    //     let res = Vector#{ };
    //     Vector.forAll(Array.compare, Vector.zip(MutList.toVector(list), res))
    //     // MutList.toVector(list) `Vector.equals` res
    // }

    // @test
    // def rangeQueryWith07(): Bool = region rc {
    //     let tree = rangeQueryDefaultTree(rc);
    //     let list = MutList.emptyWithOrder(rc);
    //     let f = k -> _ -> MutList.push(k, list);
    //     BPlusTree.rangeQueryWith(f, 7, 7, tree);
    //     let res = Vector#{ };
    //     Vector.forAll(Array.compare, Vector.zip(MutList.toVector(list), res))
    //     // MutList.toVector(list) `Vector.equals` res
    // }

    // @test
    // def rangeQueryWith08(): Bool = region rc {
    //     let tree = rangeQueryMultipleValues(rc);
    //     let list = MutList.emptyWithOrder(rc);
    //     let f = k -> v -> MutList.push((k, v), list);
    //     BPlusTree.rangeQueryWith(f, 0, 3, tree);
    //     let res = Vector#{(0, 12), (1, 12), (2, 13), (3, 14)};
    //     Vector.forAll(Array.compare, Vector.zip(MutList.toVector(list), res))
    //     // MutList.toVector(list) `Vector.equals` res
    // }

}
