def getRandomListOfPairs(n: Int32): List[(Int64, Int64)] \ Random =
    List.map(_ -> (Random.randomInt64(), Random.randomInt64()), List.range(0, n))

def getRandomListOfPairsInPieces(n: Int32, pieceSize: Int32): InsertLists \ Random =
    Vector.map(_ -> getRandomListOfPairs(pieceSize), Vector.range(0, n / pieceSize))
    // List.map(_ -> (Random.randomInt64(), Random.randomInt64()), List.range(0, n))

type alias InsertLists = Vector[List[(Int64, Int64)]]
type alias PiecewiseInsertLists = Vector[InsertLists]

// def runSingleTest(toInsert: InsertLists): Int64 \ IO = region rc {
//     Clock.runWithIO(() -> {
//         let start = Clock.currentTime(TimeUnit.Nanoseconds);
//         let tree: BPlusTree[Int64, Int64, rc]  = BPlusTree.empty(rc, 10);
//         let _: Unit = region rc2 {
//             unchecked_cast(
//                 Vector.forEach(list -> spawn unchecked_cast(() ->
//                     List.forEach(p -> {
//                         let (x, y) = p;
//                         BPlusTree.insert(x, y, tree)
//                     }, list) as Unit -> Unit \ IO)() @ rc2
//                 , toInsert)
//             as _ \ rc)
//         };
//         let end = Clock.currentTime(TimeUnit.Nanoseconds);
//         end - start
//     })
// }

// def runNTests(testNum: Int32, toInsert: InsertLists): Vector[Int64] \ IO =
//     let times = Vector.map(_ -> runSingleTest(toInsert), Vector.range(0, testNum));
//     times

// def runWithThreadsRandom(testNum: Int32, threadsNum: Int32, insertNumPerThread: Int32): Vector[Int64] \ IO + NonDet =
//     let pairs = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(insertNumPerThread), Vector.range(0, threadsNum)));
//     runNTests(testNum, pairs)



// def insertUntil(toInsert: PiecewiseInsertLists, timeLimit: Int64): Int64 \ IO = region rc {
//     let threadNum = Vector.size(toInsert);
//     let reffNumVec = Vector.map(_ -> Ref.fresh(rc, 0i64), Vector.range(0, threadNum));
//     Clock.runWithIO(() -> {
//         let start = Clock.currentTime(TimeUnit.Nanoseconds);
//         let tree: BPlusTree[Int64, Int64, rc]  = BPlusTree.empty(rc, 10);
//         let _: Unit = region rc2 {
//             unchecked_cast(
//                 Vector.forEach(match (listt, ref) -> spawn unchecked_cast(() ->
//                 Ref.put (Vector.foldRightWithCont(list -> f -> {
//                     List.forEach(p -> {
//                         let (x, y) = p;
//                         BPlusTree.insert(x, y, tree)
//                     }, list);
//                     if(Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start < timeLimit) 
//                         f() + 1i64
//                      else 0i64
//                     }
//                     , 0i64, listt), ref)
//                      as Unit -> Unit \ IO)() @ rc2
//                 , Vector.zip(toInsert, reffNumVec))
//             as _ \ rc)
//         };
//         Vector.foldLeft(acc -> x -> acc + Ref.get(x), 0i64, reffNumVec)
//         // let end = Clock.currentTime(TimeUnit.Nanoseconds);
//         // end - start
//     })
// }

// def runNTests(testNum: Int32, toInsert: PiecewiseInsertLists, timeLimit: Int64): Vector[Int64] \ IO =
//     let times = Vector.map(_ -> insertUntil(toInsert, timeLimit), Vector.range(0, testNum));
//     times

// def runWithThreadsRandom(testNum: {testNum = Int32}, threadNum: {threadNum = Int32}, maxInsert: {maxInsert = Int32}, pieceSize: {pieceSize = Int32}, timeLimit: Int64): Vector[Int64] \ IO + NonDet =
//     let pairs = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairsInPieces(maxInsert#maxInsert, pieceSize#pieceSize), Vector.range(0, threadNum#threadNum)));
//     runNTests(testNum#testNum, pairs, timeLimit)







def repeatUntil(f: Unit -> Unit \ ef1, stopFunc: Unit -> Bool \ ef2): Int64 \ ef1 + ef2 = 
    def repeatNInternal(count: Int64): Int64 \ ef1 + ef2 = {
        if (stopFunc()) count else {
            f(); repeatNInternal(count + 1i64)
        }
    };
    repeatNInternal(0i64)



def insertUntil(toInsert: InsertLists, timeLimit: Int64): Int64 \ IO = region rc {
    let threadNum = Vector.size(toInsert);
    let reffNumVec = Vector.map(_ -> Ref.fresh(rc, 0i64), Vector.range(0, threadNum));
    Clock.runWithIO(() -> {
        let start = Clock.currentTime(TimeUnit.Nanoseconds);
        let tree: BPlusTree[Int64, Int64, rc]  = BPlusTree.empty(rc, 10);
        let _: Unit = region rc2 {
            unchecked_cast(
                Vector.forEach(match (listt, ref) -> spawn unchecked_cast(() ->
                Ref.put (Vector.foldRightWithCont(list -> f -> {
                    List.forEach(p -> {
                        let (x, y) = p;
                        BPlusTree.insert(x, y, tree)
                    }, list);
                    if(Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start < timeLimit) 
                        f() + 1i64
                     else 0i64
                    }
                    , 0i64, listt), ref)
                     as Unit -> Unit \ IO)() @ rc2
                , Vector.zip(toInsert, reffNumVec))
            as _ \ rc)
        };
        // Vector.foldLeft(acc -> x -> acc + Ref.get(x), 0i64, reffNumVec)
    })
}

def runNTests(testNum: Int32, toInsert: InsertLists, timeLimit: Int64): Vector[Int64] \ IO =
    let times = Vector.map(_ -> insertUntil(toInsert, timeLimit), Vector.range(0, testNum));
    times

def runWithThreadsRandom(testNum: {testNum = Int32}, threadNum: {threadNum = Int32}, totalInserts: {totalInserts = Int32}, timeLimit: Int64): Vector[Int64] \ IO + NonDet =
    let pairs = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts), Vector.range(0, threadNum#threadNum)));
    runNTests(testNum#testNum, pairs, timeLimit)

def main04(): Unit \ IO + NonDet = {
    let secondLimit = 60i64;
    // let pairs = Random.runWithIO(() -> getRandomListOfPairs(10_000));
    let res = runWithThreadsRandom(testNum = 1, threadNum = 1, totalInserts=10_000, secondLimit * 1_000_000_000i64);
    println(res);
   // let _ = runNTests(4, pairs);
    ()
}

// def main06(): Unit \ IO = {
//     Clock.runWithIO(() -> {
//         let start = Clock.currentTime(TimeUnit.Nanoseconds);
//         repeatUntil(() -> println("x"), () -> Clock.currentTime(TimeUnit.Nanoseconds) - start > 1000000i64);
//         ()
//     });
//     ()
// }