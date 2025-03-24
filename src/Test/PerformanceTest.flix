import java.lang.System

def getRandomListOfPairs(n: Int32): List[(Int64, Int64)] \ Random =
    List.map(_ -> (Random.randomInt64(), Random.randomInt64()), List.range(0, n))


type alias InsertLists = Vector[List[(Int64, Int64)]]
type alias PiecewiseInsertLists = Vector[InsertLists]

def runSingleTest(toInsert: InsertLists): Int64 \ IO = region rc {
    Clock.runWithIO(() -> {
        let start = Clock.currentTime(TimeUnit.Nanoseconds);
        let tree: BPlusTree[Int64, Int64, rc]  = BPlusTree.empty(rc, 10);
        let _: Unit = region rc2 {
            unchecked_cast(
                Vector.forEach(list -> spawn unchecked_cast(() ->
                    List.forEach(p -> {
                        let (x, y) = p;
                        BPlusTree.insert(x, y, tree)
                    }, list) as Unit -> Unit \ IO)() @ rc2
                , toInsert)
            as _ \ rc)
        };
        let end = Clock.currentTime(TimeUnit.Nanoseconds);
        end - start
    })
}

def runNTests(testNum: Int32, toInsert: InsertLists): Vector[Int64] \ IO + Sys =
    let times = Vector.map(_ -> {System.gc(); runSingleTest(toInsert)}, Vector.range(0, testNum));
    times

def runWithThreadsRandom(testNum: Int32, threadsNum: Int32, totalInsert: Int32): Vector[Int64] \ IO + NonDet + Sys =
    let pairs = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(totalInsert / threadsNum), Vector.range(0, threadsNum)));
    runNTests(testNum, pairs)



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



def insertUntil(toInsert: InsertLists, timeLimit: Int64, order: Int32): Int64 \ IO = region rc {
    let threadNum = Vector.size(toInsert);
    let insertNum = List.size(Vector.get(0, toInsert));
    Int32.toInt64(insertNum) * Int32.toInt64(threadNum) * Clock.runWithIO(() -> {
        let start = Clock.currentTime(TimeUnit.Nanoseconds);
        let timeFunc = () -> Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start > timeLimit;
        let insertFunc: (Unit -> Unit \ IO + rc) = () -> region rc2 {
                let tree: BPlusTree[Int64, Int64, rc]  = BPlusTree.empty(rc, order);
                Vector.forEach(match list -> spawn unchecked_cast(() ->
                    List.forEach(p -> {
                        let (x, y) = p;
                        BPlusTree.insert(x, y, tree)
                    }, list)
                    
                     as Unit -> Unit \ IO)() @ rc2
                , toInsert)
        };
        repeatUntil(insertFunc, timeFunc)
        // Vector.foldLeft(acc -> x -> acc + Ref.get(x), 0i64, reffNumVec)
    })
}

def runNTestsUntil(testNum: Int32, toInsert: InsertLists, timeLimit: Int64, order: Int32): Vector[Int64] \ IO + Sys =
    let times = Vector.map(_ -> {System.gc(); insertUntil(toInsert, timeLimit, order)}, Vector.range(0, testNum));
    times

def runWithThreadsRandomUntil(testNum: {testNum = Int32}, threadNum: {threadNum = Int32}, totalInserts: {totalInserts = Int32}, timeLimit: Int64, order: Int32): Vector[Int64] \ IO + NonDet + Sys =
    let pairs = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts / threadNum#threadNum), Vector.range(0, threadNum#threadNum)));
    runNTestsUntil(testNum#testNum, pairs, timeLimit, order)


def readUntil(toInsert: InsertLists, lookup: InsertLists, timeLimit: Int64): Int64 \ IO = region rc {
    let threadNum = Vector.size(toInsert);
    let insertNum = List.size(Vector.get(0, toInsert));
    let tree: BPlusTree[Int64, Int64, rc]  = BPlusTree.empty(rc, 10);
    Vector.forEach(List.forEach(match (x, y) -> BPlusTree.insert(x, y, tree)), toInsert);
    Int32.toInt64(insertNum) * Int32.toInt64(threadNum) * Clock.runWithIO(() -> {
        let start = Clock.currentTime(TimeUnit.Nanoseconds);
        let timeFunc = () -> Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start > timeLimit;
        let insertFunc: (Unit -> Unit \ IO) = () -> region rc2 {
                Vector.forEach(match list -> spawn unchecked_cast(() ->
                    List.forEach(p -> {
                        let (x, _) = p;
                        BPlusTree.memberOfThreadUnsafe(x, tree);
                        ()
                    }, list)
                     as Unit -> Unit \ IO)() @ rc2
                , lookup)
        };
        repeatUntil(insertFunc, timeFunc)
        // Vector.foldLeft(acc -> x -> acc + Ref.get(x), 0i64, reffNumVec)
    })
}

def runNTestsReadUntil(testNum: Int32, toInsert: InsertLists, lookup: InsertLists, timeLimit: Int64): Vector[Int64] \ IO + Sys =
    let times = Vector.map(_ -> {System.gc(); readUntil(toInsert, lookup, timeLimit)}, Vector.range(0, testNum));
    times

def runWithThreadsReadRandomUntil(testNum: {testNum = Int32}, threadNum: {threadNum = Int32}, totalInserts: {totalInserts = Int32}, generatedReads: {generatedReads = Int32}, timeLimit: Int64): Vector[Int64] \ IO + NonDet + Sys =
    let inserted = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts), Vector.range(0, threadNum#threadNum)));
    let lookup = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(generatedReads#generatedReads), Vector.range(0, threadNum#threadNum)));
    runNTestsReadUntil(testNum#testNum, inserted, lookup, timeLimit)




def mainBTreeExperiment(): Unit \ IO + NonDet + Sys = 
    insertElementsDifferentOrder();
    insertFewElementsOften();
    insertManyElements();
    ()


def readExperiment(): Unit \ IO + NonDet + Sys = {
    let secondLimit = 60i64;
    let nanoLimit = secondLimit * 1_000_000_000i64;
    println("Experiment with 10 million inserts");
    Vector.forEach(inserts -> {
        println("Inserts");
        println(inserts);
        println(runWithThreadsReadRandomUntil(testNum = 20, threadNum = 1, totalInserts = inserts, generatedReads = 50_000_000, nanoLimit))
    }, Vector#{1_000_000})
}
def insertManyElements(): Unit \ IO + NonDet + Sys = {
    println("Experiment with 10 million inserts");
    Vector.forEach(threads -> {
        println("Threads");
        println(threads);
        println(runWithThreadsRandom(20, threads, 10_000_000))
    }, Vector.range(1, 40))
}

def insertElementsDifferentOrder(): Unit \ IO + NonDet + Sys = {
    let secondLimit = 60i64;
    let nanoLimit = secondLimit * 1_000_000_000i64;
    println("Experiment with different order:");
    Vector.forEach(order -> Vector.forEach(insertNum -> 
        Vector.forEach(threads -> {
            println("Order:");
            println(order);
            println("Insertions:");
            println(insertNum);
            println("Threads:");
            println(threads);
            println(runWithThreadsRandomUntil(testNum = 20, threadNum = threads, totalInserts = insertNum, nanoLimit, order))
        }, Vector#{1, 2, 5, 10, 20}), Vector#{10_000, 1_000_000}), Vector#{10, 20, 40, 60})
}

def insertFewElementsOften(): Unit \ IO + NonDet + Sys = {
    println("Experiment with low height:");
    let secondLimit = 60i64;
    let nanoLimit = secondLimit * 1_000_000_000i64;
    Vector.forEach(insertNum -> 
        Vector.forEach(threads -> {
            println("Insertions:");
            println(insertNum);
            println("Threads:");
            println(threads);
            println(runWithThreadsRandomUntil(testNum = 20, threadNum = threads, totalInserts=insertNum, nanoLimit, 10))
        }, Vector.range(1, 41)), 
    Vector#{10_000, 1_000_000})
}
