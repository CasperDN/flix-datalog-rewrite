import java.util.concurrent.locks.ReentrantLock
import java.lang.Float
import java.lang.System;

def testLink(n: Int32, order: Int32): Unit \ IO = region rc {
    let start = System.currentTimeMillis();
    let tree = BPlusTree.empty(rc, order);
    let pairs = List.map(p -> {
        let (x, y) = p;
        (Int32.modulo(x * 1000, 1091), Int32.modulo(y * 1003, 109))
    }, List.zip(List.range(1, n), List.reverse(List.range(1, n))));
    List.forEach(p -> {
        let (x, y) = p;
        BPlusTree.insert(x, y, tree)
    }, pairs);
    BPlusTree.memberOf(0, tree);
    let end = System.currentTimeMillis();
    println(end-start);
    ()
}

def testRedBlack(n: Int32): Unit \ IO = region rc {
    let start = System.currentTimeMillis();
    let tree = MutMap.empty(rc);
    let pairs = List.map(p -> {
        let (x, y) = p;
        (Int32.modulo(x * 1000, 1091), Int32.modulo(y * 1003, 109))
    }, List.zip(List.range(1, n), List.reverse(List.range(1, n))));
    List.forEach(p -> {
        let (x, y) = p;
        MutMap.put(x, y, tree)
    }, pairs);
    println(MutMap.memberOf(0, tree));
    let end = System.currentTimeMillis();
    println(end-start);
    ()
}

def testMultiMap(n: Int32): Unit \ IO =
    let start = System.currentTimeMillis();
    let pairs = List.map(p -> {
        let (x, y) = p;
        (Int32.modulo(x * 1000, 1091), Int32.modulo(y * 1003, 109))
    }, List.zip(List.range(1, n), List.reverse(List.range(1, n))));
    let tree = List.foldLeft(acc -> p -> {
        let (x, y) = p;
        MultiMap.insert(x, y, acc)
    }, MultiMap.empty(), pairs);
    println(MultiMap.memberOf(0, tree));
    let end = System.currentTimeMillis();
    println(end-start);
    ()


def testLinkRandom(vec: Vector[Int32], order: Int32): Unit \ IO = region rc {
    let start = System.currentTimeMillis();
    let tree = BPlusTree.empty(rc, order);
    Vector.forEach(x -> {
        BPlusTree.insert(x, 0, tree)
    }, vec);
    BPlusTree.memberOf(0, tree);
    let end = System.currentTimeMillis();
    println(end-start);
    ()
}

def testRedBlackRandom(vec: Vector[Int32]): Unit \ IO = region rc {
    let start = System.currentTimeMillis();
    let tree = MutMap.empty(rc);
    Vector.forEach(x -> {
        MutMap.put(x, 0, tree)
    }, vec);
    println(MutMap.memberOf(0, tree));
    let end = System.currentTimeMillis();
    println(end-start);
    ()
}

def testMultiMapRandom(vec: Vector[Int32]): Unit \ IO =
    let start = System.currentTimeMillis();
    let tree = Vector.foldLeft(acc -> x -> {
        MultiMap.insert(x, 0, acc)
    }, MultiMap.empty(), vec);
    println(MultiMap.memberOf(0, tree));
    let end = System.currentTimeMillis();
    println(end-start);
    ()


def main(): Unit \ IO =
    let n = 10_000_000;
    let vec = (Random.handleWithSeed(0i64, () -> Vector.map(_ -> Random.randomInt32(), Vector.range(0, n))))();
    println(Vector.last(vec));
    testLink(n, 20);
    testRedBlack(n);
    testMultiMap(n);
    testLinkRandom(vec, 20);
    testRedBlackRandom(vec);
    testMultiMapRandom(vec);

    ()
