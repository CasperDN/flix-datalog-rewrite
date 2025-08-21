def latticeTest(): Unit \ IO =
    println("Starting");
    let func = () -> {
        let start = Clock.currentTime(TimeUnit.Seconds);
        let map = List.map(x -> (x, x + 1), List.range(1, 200));
        let injected = inject map into Edge/2;
        let path = injected <+> #{
            Path(x, y; Down.Down(1)) :- Edge(x, y).
            Path(x, y; n + Down.Down(1)) :- Path(x, z; n), Edge(z, y).
        };
        let r = query path select (x, y, set) from Path(x,y; set);
        let x = Vector.head(r);
        if (Option.isEmpty(x)) {
            let end = Clock.currentTime(TimeUnit.Seconds);
            println("Took: ${end - start} s")
        } else {
            let end = Clock.currentTime(TimeUnit.Seconds);
            println("Took: ${end - start} s")
        }
    };
    Clock.runWithIO(() -> repeatN(func, 10))

def main(): Unit \ IO =
    println("Starting");
    let func = () -> {
        let start = Clock.currentTime(TimeUnit.Seconds);
        let map = List.map(x -> (x, x + 1), List.range(1, 1000));
        let injected = inject map into Edge/2;
        let path = injected <+> #{
            Edge(x, y) :- Edge(y, x).
            Path(x, y) :- Edge(x, y).
            Path(x, y) :- Path(x, z), Edge(z, y).
        };
        let r = query path select (x, y) from Path(x,y);
        let x = Vector.head(r);
        if (Option.isEmpty(x)) {
            let end = Clock.currentTime(TimeUnit.Seconds);
            println("Took: ${end - start} s")
        } else {
            let end = Clock.currentTime(TimeUnit.Seconds);
            println("Took: ${end - start} s")
        }
    };
    Clock.runWithIO(() -> repeatN(func, 10));
    ()

def repeatN(f: Unit -> Unit \ ef, num: Int32): Unit \ef =
    if (num <= 0) {
        ()
    } else {
        f();
        repeatN(f, num - 1)
    }

def ++++++(x: Int32, y: Int32): Int32 = Int32.modulo(x, y)

def isPrime(x: Int32): Bool =
    def loop(i) =
        if (i > x / 2) true
        else if (x ++++++ i == 0) false
        else loop(i+1);
    if (x < 2) false
    else loop(2)

def primesInRange(b: Int32, e: Int32): Vector[Int32] =
    Vector.range(b, e) |> Vector.filter(isPrime)

def inc(x: Int32): Int32 = x + 1

def main3(): Unit \ IO =
    let r = #{
        P(1).
        Q(20).
        R(p, inc(p)) :- P(b), Q(e), let p = primesInRange(b, e).
    };
    println(query r select (p, q) from R(p, q))

pub def main111(): Unit \ IO =
    let rules = #{
        Foo("a", 1).
        Foo("b", 2).

        Bar(n; v) :- Foo(n, v).
    };
    query rules select (x, y) from Bar(x; y) |> println;
    ()

def main99(): Unit \ IO =
    println("Print");
    let path = #{
        Edge(1,2).

        Path(x, y) :- Edge(x, y).
        Path(x, y) :- Path(x, z), Path(z, y).
    };
    let indexSelection1 = #{
        A(1, 2, 3).
        B(1, 2, 3).
        B(x, y, z) :- A(x, y, z), B(x, _, z).
        B(x, y, z) :- A(x, y, z), B(x, _, _).
        B(x, y, z) :- A(x, y, z), B(x, y, _).
        B(x, y, z) :- A(x, y, z), B(x, y, z).
    };
    let indexSelection2 = #{
        A(1, 2, 3).
        B(1, 2, 3).
        B(x, y, z) :- A(x, y, z), B(x, _, z).
        B(x, y, z) :- A(x, y, z), B(x, y, _).
        B(x, y, z) :- A(x, y, z), B(x, y, z).
    };
    println("Print2");
    let _ = query path select (x, y) from Path(x,y);
    println("Print3");
    let r = query indexSelection1 select (x, y, z) from B(x, y, z);
    println("Print4");
    let _ = query indexSelection2 select (x, y, z) from B(x, y, z);
    println("Print5");
    println(r);
    println("Print6");
    ()

def sum1(x: Int32): Int32 = x
def sum2(x: Int32, y: Int32): Int32 = x + y
def sum3(x: Int32, y: Int32, z: Int32): Int32 = x + y + z
def sum4(x: Int32, y: Int32, z: Int32, w: Int32): Int32 = x + y + z + w
def sum5(x: Int32, y: Int32, z: Int32, w: Int32, v: Int32): Int32 = x + y + z + w + v

pub def mainApp(): Unit \ IO =
    let rules = #{
        Foo1(1).
        Foo2(2).
        Foo3(3).
        Foo4(4).
        Foo5(5).

        Bar(a,
            sum1(a),
            sum2(a, b),
            sum3(a, b, c),
            sum4(a, b, c, d),
            sum5(a, b, c, d, e)
        ) :- Foo1(a), Foo2(b), Foo3(c), Foo4(d), Foo5(e).
    };
    query rules select (a, b, c, d, e, f) from Bar(a, b, c, d, e, f) |> println;
    ()

pub def pathh(): Unit \ IO =
    let edges = List.range(0,1000) |> List.map(i -> (i, i+1));
    let f = inject edges into Edge/2;
    let r = #{
        A(1).
        Path(x, y) :- Edge(x, y).
        Path(x, z) :- Edge(y, z), Path(x, y).
        // DumbRule(1,2,3) :- Path(x, 1), A(x).
    };
    query f, r select (x, y) from Path(x, y) |> Vector.head |> println

pub def dumb3333(): Unit \ IO =
    let r = #{
        A(1).
    };
    query r select x from A(x) |> Vector.head |> println;
    ()

pub def dumb(): Unit \ IO =
    let aFacts = List.range(0,101);
    let bFacts = List.range(0,10);
    let f1 = inject aFacts into A/1;
    let f2 = inject bFacts into B/1;
    let r = #{
        A(x) :- D(x).
        D(x) :- A(x).
        B(x) :- D(x).
        C(x) :- A(x), B(x).
    };
    query f1, f2, r select x from C(x)  |> println;
    ()


def forceEval(): Unit \ IO = {
    println("Hej")
}


def testFunctionalF1X2_01(): Bool =
let ff = _x -> Vector#{};
    let pr = #{
        A(1).
        R(a, b) :- A(x), let (a, b) = ff(x).
    };
    let actual = query pr select (x, y) from R(x, y);
    Assert.eq((Vector#{}: Vector[(Int32, Int32)]), actual)

def runForever(): Unit \ IO = {
    if (testFunctionalF1X2_01()) runForever() else runForever()
}


def runN(n: Int32): Unit \ IO = {
    if (testFunctionalF1X2_01() and n > 0) runN(n - 1) else ()
}

def main1000(): Unit \ IO = {
    let now = Clock.runWithIO(Clock.now);
    runN(80000);
    println((Clock.runWithIO(Clock.now) - now) / 1000i64);
    ()
}


// @test
// def fffff(): Bool = {
//     let db = #{
//         A(1). A(3). A(5).
//         // B(2). B(7). B(11).
//     };
//     let pr = #{
//         R(x * y) :- A(x), let y = Vector#{2, 7, 11}, if (x <= y).
//     };
//     let pp = pquery db, pr select R(21) with {A};
//     Vector.map(v -> ematch v {
//         case A(x) => "A(${x})"
//     }, pp) `Assert.eq` Vector#{"A(3)", "B(7)"}
// }

@test
def f5(): Bool = {
    let db = #{
        A(1). A(3). A(5).
    };
    let pr = #{
        R(x * y) :- A(x), let y = Vector#{2, 7, 11}, if (x <= y).
    };
    let pp = pquery db, pr select R(21) with {A};
    Vector.map(v -> ematch v {
        case A(x) => "A(${x})"
    }, pp) `Assert.eq` Vector#{"A(3)"}
}



mod BPlusTree {
    ///
    /// Returns `Some((k, v))` if `k => v` is in `t`. Otherwise, returns `None`.
    ///
    /// Thread-safe.
    ///
    pub def getPair(k: k, t: BPlusTree[k, v, r]): Option[(k, v)] \ r with Order[k] = {
        let (leaf, stamp) = BPlusTree.findLeaf(k, t);
        Node.getPair(k, stamp, leaf, t)
    }

    ///
    /// Updates the tree `t` with the mapping `k => v`. Replaces any
    /// existing mapping, `k2 => v2` mapping if `decider(k, v, k2, v2) == true`.
    ///
    /// Thread-safe and atomic.
    ///
    pub def putIf(k: k, v: v, decider: k -> v -> k -> v -> Bool, t: BPlusTree[k, v, r]): Unit \ r with Order[k] =
        fixRoot(putIfInternal(k, v, decider, t), t)


    ///
    /// Internal method for `putIf`.
    ///
    /// Called when restarting.
    ///
    /// Returns the `Some(newRoot, stamp)` if the root was split where `stamp` is a write-stamp
    /// on `rootLock`.
    ///
    def putIfInternal(k: k, v: v, decider: k -> v -> k -> v -> Bool, t: BPlusTree[k, v, r]): Option[(Node[k, v, r], Int64)] \ r with Order[k] =
        let (leaf, stamp) = BPlusTree.findLeaf(k, t);
        Node.insertIntoLeafIf(k, v, decider, leaf, stamp, t)


    mod Node {
        use BPlusTree.Lock

        ///
        /// Returns `Some((key, value))` if `key => val` is in `tree`. Otherwise return `None`.
        ///
        @Internal
        pub def getPair(key: k, stamp: Int64, node: Node[k, v, r], tree: BPlusTree[k, v, r]): Option[(k, v)] \ r with Order[k] =
            let index = binarySearch(key, BPlusTree.search(tree), node);
            let result = if (index < 0)
                None
            else
                Some((Array.get(index, node->keys), Array.get(index, node->values)));
            if (not Lock.valid(stamp, node->lock)) {
                // Restart
                Lock.yieldBasedOn(node->lock);
                BPlusTree.getPair(key, tree)
            } else {
                result
            }

        ///
        /// Inserts the mapping `key => val` into the leaf `node` if it is not already present
        /// Otherwise if the mapping `key2 => val2` is presents overwrite the mapping by `key => val`,
        /// if `decider(key, val, key2, val2) == true`. If a split is caused return the new root.
        ///
        /// Lock invariants:
        ///
        /// - On invocation, `stamp` is an optimistic stamp on `node->lock`.
        ///
        /// - On return, the thread has no lock on the tree if the returned value is None.
        ///   Otherwise it has a write-lock on `tree->rootLock` and `p` where `Some(p)` is returned
        ///
        @Internal
        pub def insertIntoLeafIf(
            key: k,
            val: v,
            decider: k -> v -> k -> v -> Bool,
            node: Node[k, v, r],
            stamp: Int64,
            tree: BPlusTree[k, v, r]
        ): Option[(Node[k, v, r], Int64)] \ r with Order[k] = {
            let search = BPlusTree.search(tree);
            let index = binarySearch(key, search, node);
            if(index < 0) {
                // `key` is not currently in tree. Attempt to gain the write lock and add it.
                insertIntoLeafForceIf(key, val, decider, node, stamp, index, tree)
            } else {
                let oldKey = Array.get(index, node->keys);
                let oldVal = Array.get(index, node->values);
                // Verify that the pair is legal/not corrupted.
                if (not Lock.valid(stamp, node->lock)) {
                    // Restart
                    Lock.yieldBasedOn(node->lock);
                    BPlusTree.putIfInternal(key, val, decider, tree)
                } else {
                    if (decider(key, val, oldKey, oldVal)) {
                        insertIntoLeafForceIf(key, val, decider, node, stamp, index, tree)
                    } else {
                        // At some point `oldKey => oldVal` was in the tree. We observed it and
                        // decided to not insert `key => val`, by `decider`.
                        None
                    }
                }
            }
        }

        ///
        /// Attempts to grab the lock of `node` and insert the `key => val` mapping. Restarts with
        /// `putIfInternal` if this is not successfull.
        ///
        /// Lock invariants:
        ///
        /// - On invocation, `stamp` is an optimistic stamp on `node->lock`.
        ///
        /// - On return, the thread has no lock on the tree if the returned value is None.
        ///   Otherwise it has a write-lock on `tree->rootLock` and `p` where `Some(p)` is returned
        ///
        @Internal
        pub def insertIntoLeafForceIf(
            key: k,
            val: v,
            decider: k -> v -> k -> v -> Bool,
            node: Node[k, v, r],
            stamp: Int64,
            index: Int32,
            tree: BPlusTree[k, v, r]
        ): Option[(Node[k, v, r], Int64)] \ r with Order[k] = {
            let writeStamp = Lock.tryConvertToWrite(stamp, node->lock);
            if (not Lock.valid(writeStamp, node->lock)) {
                // Restart
                Lock.yieldBasedOn(node->lock);
                BPlusTree.putIfInternal(key, val, decider, tree)
            } else {
                insertIntoLeafPropagate(key, val, index, node, writeStamp, tree)
            }
        }

    }
}

@Test
def testPQueryWithCycle01(): Bool =
    let db = #{
        Edge(1, 2). Edge(2, 1).
    };
    let pr = #{
        Path(x, y) :- Edge(x, y).
        Path(x, z) :- Path(x, y), Edge(y, z).
        Cycle(x)   :- Path(x, x).
    };
    let pp = pquery db, pr select Cycle(1) with {Edge};
    Vector.map(v -> ematch v { case Edge(x, y) => (x, y) }, pp) `Assert.eq` Vector#{(1, 2), (2, 1)}

def main9384(): Bool = {
    let db = #{
        A(1). A(2). A(3). A(4). A(5).
    };
    let pr = #{
        B(1) :- not A(-1).
        B(x + 1) :- B(x), A(x).
        C(-1) :- not B(-2).
        C(x) :- B(x).
        C(x) :- A(x), C(-1).
    };
    let pp = pquery db, pr select C(5) with {A};
    Vector.map(v -> ematch v {
        case A(x) => x
    }, pp) `Assert.eq` Vector#{5}
}
