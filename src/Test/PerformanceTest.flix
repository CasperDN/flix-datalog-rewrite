// import java.lang.System
// import java.util.TreeMap
// import java.lang.Long

// def standardOrder(): Int32 = 64

// def commonTimeLimitNano(): Int64 = 60i64 * 1_000_000_000i64
// def repeatNum(): Int32 = 10

// def defaultSearch(): Vector[Int32] = Vector#{0,1,2}


// def readNum(): Int32 = 1_000_000

// def mainBTreeExperiment(): Unit \ IO + NonDet + Sys = 
//     let _ = Random.runWithIO(() -> Clock.runWithIO(() -> FileWrite.runWithIO(() ->{
//     // insertElementsDifferentOrder();
//     // insertFewElementsOften();
//     // insertManyElements();
//     insertExperiment();
//     readExperiment();
//     flixInsertExperiment();
//     flixReadExperiment();
//     // javaInsertExperiment();
//     // javaReadExperiment();
//     ()})));
//     ()



// def getRandomListOfPairs(n: Int32, rc: Region[r]): List[(Array[Int64, r], Int64)] \ Random + r =
//     List.map(_ -> (Array#{Random.randomInt64(), Random.randomInt64(), Random.randomInt64()} @ rc, Random.randomInt64()), List.range(0, n))


// type alias InsertLists[r: Region] = Vector[List[(Array[Int64, r], Int64)]]

// def runSingleTest(rc: Region[r], toInsert: InsertLists[r]): Int64 \ IO + r + Clock =
//     // Clock.runWithIO(() -> {
//         let start = Clock.currentTime(TimeUnit.Nanoseconds);
//         let tree = BPlusTree.empty(rc, standardOrder(), defaultSearch());
//         let _: Unit = region rc2 {
//             Vector.forEach(list -> spawn unchecked_cast(() ->
//                 List.forEach(p -> {
//                     let (x, y) = p;
//                     BPlusTree.insert(x, y, tree)
//                 }, list) as Unit -> Unit \ IO)() @ rc2
//             , toInsert)
//         };
//         let end = Clock.currentTime(TimeUnit.Nanoseconds);
//         end - start
//     // })


// def runNTestsGeneral(testNum: Int32, func: Unit -> Int64 \ ef): Vector[Int64] \ IO + Sys + ef =
//     let times = Vector.map(_ -> {System.gc(); func()}, Vector.range(0, testNum));
//     times

// def runWithThreadsRandom(rc: Region[r], testNum: Int32, threadsNum: Int32, totalInsert: Int32): Vector[Int64] \ IO + Random + Sys + r + Clock =
//     let pairs = Vector.map(_ -> getRandomListOfPairs(totalInsert / threadsNum, rc), Vector.range(0, threadsNum));
//     runNTestsGeneral(testNum, () -> runSingleTest(rc, pairs))


// def repeatUntil(f: Unit -> Unit \ ef1, stopFunc: Unit -> Bool \ ef2): Int64 \ ef1 + ef2 = 
//     def repeatNInternal(count: Int64): Int64 \ ef1 + ef2 = {
//         if (stopFunc()) count else {
//             f(); repeatNInternal(count + 1i64)
//         }
//     };
//     repeatNInternal(0i64)



// def insertUntil(rc: Region[r], toInsert: InsertLists[r], timeLimit: Int64, order: Int32): Int64 \ IO + Clock + r = 
//     let threadNum = Vector.size(toInsert);
//     let insertNum = List.size(Vector.get(0, toInsert));
//     Int32.toInt64(insertNum) * Int32.toInt64(threadNum) * {
//         let start = Clock.currentTime(TimeUnit.Nanoseconds);
//         let timeFunc = () -> Clock.currentTime(TimeUnit.Nanoseconds) - start > timeLimit;
//         let insertFunc: (Unit -> Unit \ IO + r) = () -> region rc2 {
//                 let tree  = BPlusTree.empty(rc, order, defaultSearch());
//                 Vector.forEach(match list -> spawn unchecked_cast(() ->
//                     List.forEach(p -> {
//                         let (x, y) = p;
//                         BPlusTree.insert(x, y, tree)
//                     }, list)
                    
//                      as Unit -> Unit \ IO)() @ rc2
//                 , toInsert)
//         };
//         repeatUntil(insertFunc, timeFunc)
//         // Vector.foldLeft(acc -> x -> acc + Ref.get(x), 0i64, reffNumVec)
//     }


// def runWithThreadsRandomUntil(rc: Region[r], testNum: {testNum = Int32}, threadNum: {threadNum = Int32}, totalInserts: {totalInserts = Int32}, timeLimit: Int64, order: Int32): Vector[Int64] \ IO + NonDet + Sys + r =
//     let pairs = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts / threadNum#threadNum, rc), Vector.range(0, threadNum#threadNum)));
//     runNTestsGeneral(testNum#testNum, () -> Clock.runWithIO(() -> insertUntil(rc, pairs, timeLimit, order)))

// def readUntil(rc: Region[r], toInsert: InsertLists[r], lookup: InsertLists[r], timeLimit: Int64): Int64 \ IO + r = 
//     let readNum = List.size(Vector.get(0, lookup));
//     let tree: BPlusTree[r]  = BPlusTree.empty(rc, standardOrder(), defaultSearch());
//     Vector.forEach(List.forEach(match (x, y) -> BPlusTree.insert(x, y, tree)), toInsert);
//     Int32.toInt64(readNum) * Clock.runWithIO(() -> {
//         let start = Clock.currentTime(TimeUnit.Nanoseconds);
//         let timeFunc = () -> Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start > timeLimit;
//         let readFunc: (Unit -> Unit \ IO) = () -> region rc2 {
//                 Vector.forEach(match list -> spawn unchecked_cast(() ->
//                     List.forEach(p -> {
//                         let (x, _) = p;
//                         BPlusTree.memberOfThreadUnsafe(x, tree);
//                         ()
//                     }, list)
//                      as Unit -> Unit \ IO)() @ rc2
//                 , lookup)
//         };
//         repeatUntil(readFunc, timeFunc)
//     })


// def runWithThreadsReadRandomUntil(rc: Region[r], testNum: {testNum = Int32}, totalInserts: {totalInserts = Int32}, generatedReads: {generatedReads = Int32}, timeLimit: Int64): Vector[Int64] \ IO + NonDet + Sys + r =
//     let inserted = Random.runWithIO(() -> Vector#{getRandomListOfPairs(totalInserts#totalInserts, rc)});
//     let lookup = Random.runWithIO(() -> Vector#{getRandomListOfPairs(generatedReads#generatedReads, rc)});
//     runNTestsGeneral(testNum#testNum, () -> readUntil(rc, inserted, lookup, timeLimit))

// def insertUntilFlixMap(toInsert: Vector[List[(Array[Int64, r], Int64)]], timeLimit: Int64): Int64 \ IO = region rc {
//     let insertNum = List.size(Vector.get(0, toInsert));
//     Int32.toInt64(insertNum) * Clock.runWithIO(() -> {
//         let start = Clock.currentTime(TimeUnit.Nanoseconds);
//         let timeFunc = () -> Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start > timeLimit;
//         let insertFunc: (Unit -> Unit \ IO) = () -> region rc2 {
//                 Vector.forEach(match list -> spawn unchecked_cast(() -> {
//             let tree  = MutMap.empty(rc);
//             List.forEach(p -> {
//                 let (x, y) = p;
//                 MutMap.put(unchecked_cast(x as Vector[Int64]), y, tree)
//             }, list)} as Unit -> Unit \ IO)() @ rc2
//         , toInsert)};
//         repeatUntil(insertFunc, timeFunc)
//     })
// }

// def runFlixMap(rc: Region[r], testNum: {testNum = Int32}, totalInserts: {totalInserts = Int32}, timeLimit: Int64): Vector[Int64] \ IO + Random + Sys + r =
//     let inserted = Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts, rc), Vector.range(0, 1));
//     runNTestsGeneral(testNum#testNum, () -> insertUntilFlixMap(inserted, timeLimit))

// def readUntilFlixMap(rc: Region[r], toInsert: Vector[List[(Array[Int64, r], Int64)]], lookup: InsertLists[r], timeLimit: Int64): Int64 \ IO + r =
//     let readNum = List.size(Vector.get(0, lookup));
//     let tree  = MutMap.empty(rc);
//     Vector.forEach(List.forEach(match (x, y) -> MutMap.put(unchecked_cast(x as Vector[Int64]), y, tree)), toInsert);
//     Int32.toInt64(readNum) * Clock.runWithIO(() -> {
//         let start = Clock.currentTime(TimeUnit.Nanoseconds);
//         let timeFunc = () -> Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start > timeLimit;
//         let readFunc: (Unit -> Unit \ IO) = () -> region rc2 {
//             Vector.forEach(match list -> spawn unchecked_cast(() -> {
//                 List.forEach(p -> {
//                     let (x, _) = p;
//                     MutMap.memberOf(unchecked_cast(x as Vector[Int64]), tree);
//                     ()
//                 }, list)} as Unit -> Unit \ IO)() @ rc2
//             , lookup)
//         };
//         repeatUntil(readFunc, timeFunc)
//     })


// def runFlixMapRead(rc: Region[r], testNum: {testNum = Int32}, totalInserts: {totalInserts = Int32}, generatedReads: {generatedReads = Int32}, timeLimit: Int64): Vector[Int64] \ IO + NonDet + Sys + r =
//     let inserted = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts, rc), Vector.range(0, 1)));
//     let lookup = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(generatedReads#generatedReads, rc), Vector.range(0, 1)));
//     runNTestsGeneral(testNum#testNum, () -> readUntilFlixMap(rc, inserted, lookup, timeLimit))

// // def insertUntilJavaMap(toInsert: Vector[List[(Int64, Int64)]], timeLimit: Int64): Int64 \ IO =
// //     let insertNum = List.size(Vector.get(0, toInsert));
// //     Int32.toInt64(insertNum) * Clock.runWithIO(() -> {
// //         let start = Clock.currentTime(TimeUnit.Nanoseconds);
// //         let timeFunc = () -> Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start > timeLimit;
// //         let insertFunc: (Unit -> Unit \ IO) = () -> region rc2 {
// //             Vector.forEach(match list -> spawn unchecked_cast(() -> {
// //                 let tree  = new TreeMap();
// //                 List.forEach(p -> {
// //                     let (x, y) = p;
// //                     tree.put(Long.valueOf(x), Long.valueOf(y));
// //                     ()
// //                 }, list)} as Unit -> Unit \ IO)() @ rc2
// //         , toInsert)};
// //         repeatUntil(insertFunc, timeFunc)
// //     })


// // def runJavaMap(testNum: {testNum = Int32}, totalInserts: {totalInserts = Int32}, timeLimit: Int64): Vector[Int64] \ IO + NonDet + Sys =
// //     let inserted = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts), Vector.range(0, 1)));
// //     runNTestsGeneral(testNum#testNum, () -> insertUntilJavaMap(inserted, timeLimit))

// def runBPlusTree(rc: Region[r], testNum: {testNum = Int32}, totalInserts: {totalInserts = Int32}, timeLimit: Int64): Vector[Int64] \ IO + Random + Sys + r + Clock =
//     let inserted = Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts, rc), Vector.range(0, 1));
//     runNTestsGeneral(testNum#testNum, () -> insertUntil(rc, inserted, timeLimit, standardOrder()))

// // def readUntilJavaMap(toInsert: Vector[List[(Int64, Int64)]], lookup: InsertLists[r], timeLimit: Int64): Int64 \ IO = 
// //     let readNum = List.size(Vector.get(0, lookup));
// //     let tree  = new TreeMap();
// //     Vector.forEach(List.forEach(match (x, y) -> {tree.put(Long.valueOf(x), Long.valueOf(y)); ()}), toInsert);
// //     Int32.toInt64(readNum) * Clock.runWithIO(() -> {
// //         let start = Clock.currentTime(TimeUnit.Nanoseconds);
// //         let timeFunc = () -> Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start > timeLimit;
// //         let readFunc: (Unit -> Unit \ IO) = () -> region rc2 {
// //                 Vector.forEach(match list -> spawn unchecked_cast(() -> {
// //                     List.forEach(p -> {
// //                         let (x, _) = p;
// //                         tree.get(Long.valueOf(x));
// //                         ()
// //                     }, list)} as Unit -> Unit \ IO)() @ rc2
// //         , lookup)};
// //         repeatUntil(readFunc, timeFunc)
// //     })


// // def runJavaMapRead(testNum: {testNum = Int32}, totalInserts: {totalInserts = Int32}, generatedReads: {generatedReads = Int32}, timeLimit: Int64): Vector[Int64] \ IO + NonDet + Sys =
// //     let inserted = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(totalInserts#totalInserts), Vector.range(0, 1)));
// //     let lookup = Random.runWithIO(() -> Vector.map(_ -> getRandomListOfPairs(generatedReads#generatedReads), Vector.range(0, 1)));
// //     runNTestsGeneral(testNum#testNum, () -> readUntilJavaMap(inserted, lookup, timeLimit))

// // def javaReadExperiment(): Unit \ IO + NonDet + Sys + FileWrite = {
// //     let reads = readNum();
// //     let file = "javaReadExperiment.txt";
// //     FileWrite.write(str = "", file);
// //     let nanoLimit = commonTimeLimitNano();
// //     FileWrite.append(str = "Java: Read experiment", file);
// //     FileWrite.append(str = "\nTotal reads: ${reads}", file);
// //     println("Java: Read experiment");
// //     Vector.forEach(inserts -> {
// //         FileWrite.append(str = "\nInserts: ", file);
// //         FileWrite.append(str = Int32.toString(inserts), file);
// //         FileWrite.append(str = "\n", file);
// //         println("Inserts");
// //         println(inserts);
// //         FileWrite.append(str = Vector.toString(runJavaMapRead(testNum = repeatNum(), totalInserts = inserts, generatedReads = reads, nanoLimit)), file)
// //     }, Vector#{10_000, 100_000, 1_000_000})
// // // }
// // def javaInsertExperiment(): Unit \ IO + NonDet + Sys + FileWrite = {
// //     let file = "javaWriteExperiment.txt";
// //     FileWrite.write(str = "", file);
// //     let nanoLimit = commonTimeLimitNano();
// //     println("Java: Insert experiment");
// //     FileWrite.append(str = "Java: Insert experiment", file);
// //     Vector.forEach(inserts -> {
// //         FileWrite.append(str = "\nInserts: ", file);
// //         FileWrite.append(str = Int32.toString(inserts), file);
// //         FileWrite.append(str = "\n", file);
// //         println("Inserts");
// //         println(inserts);
// //         FileWrite.append(str = Vector.toString(runJavaMap(testNum = repeatNum(), totalInserts = inserts, nanoLimit)), file)
// //     }, Vector#{10_000, 100_000, 1_000_000})
// // }

// def flixInsertExperiment(): Unit \ IO + Random + Sys + FileWrite = region rc {
//     let file = "flixWriteExperiment.txt";
//     FileWrite.write(str = "", file);
//     let nanoLimit = commonTimeLimitNano();
//     FileWrite.append(str = "Flix: Insert experiment", file);
//     println("Flix: Insert experiment");
//     Vector.forEach(inserts -> {
//         FileWrite.append(str = "\nInserts: ", file);
//         FileWrite.append(str = Int32.toString(inserts), file);
//         FileWrite.append(str = "\n", file);
//         println("Inserts");
//         println(inserts);
//         FileWrite.append(str = Vector.toString(runFlixMap(rc, testNum = repeatNum(), totalInserts = inserts, nanoLimit)), file)
//     }, Vector#{10_000, 100_000, 1_000_000})
// }

// def flixReadExperiment(): Unit \ IO + NonDet + Sys + FileWrite = region rc {
//     let reads = readNum();
//     let file = "flixReadExperiment.txt";
//     FileWrite.write(str = "", file);
//     let nanoLimit = commonTimeLimitNano();
//     FileWrite.append(str = "Flix: Read experiment", file);
//     FileWrite.append(str = "\nTotal reads: ${reads}", file);
//     println("Flix: Read experiment");
//     Vector.forEach(inserts -> {
//         FileWrite.append(str = "\nInserts: ", file);
//         FileWrite.append(str = Int32.toString(inserts), file);
//         FileWrite.append(str = "\n", file);
//         println("Inserts");
//         println(inserts);
//         FileWrite.append(str = Vector.toString(runFlixMapRead(rc, testNum = repeatNum(), totalInserts = inserts, generatedReads = reads, nanoLimit)), file)
//     }, Vector#{10_000, 100_000, 1_000_000})
// }

// def readExperiment(): Unit \ IO + NonDet + Sys + FileWrite = region rc {
//     let reads = readNum();
//     let file = "BPlusTreeReadExperiment.txt";
//     FileWrite.write(str = "", file);
//     let nanoLimit = commonTimeLimitNano();
//     FileWrite.append(str = "BPlusTree: Read experiment", file);
//     FileWrite.append(str = "\nTotal reads: ${reads}", file);
//     println("BPlusTree: Read experiment");
//     Vector.forEach(inserts -> {
//         FileWrite.append(str = "\nInserts: ", file);
//         FileWrite.append(str = Int32.toString(inserts), file);
//         FileWrite.append(str = "\n", file);
//         println("Inserts");
//         println(inserts);
//         FileWrite.append(str = Vector.toString(runWithThreadsReadRandomUntil(rc, testNum = repeatNum(), totalInserts = inserts, generatedReads = reads, nanoLimit)), file)
//     }, Vector#{10_000, 100_000, 1_000_000})
// }

// def insertExperiment(): Unit \ IO + Random + Sys + Clock + FileWrite = region rc {
//     let file = "BPlusTreeWriteExperiment.txt";
//     FileWrite.write(str = "", file);
//     let nanoLimit = commonTimeLimitNano();
//     println("BPlusTree: Insert experiment");
//     FileWrite.append(str = "BPlusTree: Insert experiment", file);
//     Vector.forEach(inserts -> {
//         FileWrite.append(str = "\nInserts: ", file);
//         FileWrite.append(str = Int32.toString(inserts), file);
//         FileWrite.append(str = "\n", file);
//         println("Inserts");
//         println(inserts);
//         FileWrite.append(str = Vector.toString(runBPlusTree(rc, testNum = repeatNum(), totalInserts = inserts, nanoLimit)), file)
//     }, Vector#{10_000, 100_000, 1_000_000})
// }
// def insertManyElements(): Unit \ IO + Random + Sys + Clock + FileWrite = region rc {
//     let file = "ManyInserts.txt";
//     FileWrite.write(str = "", file);
//     FileWrite.append(str = "Experiment with 10 million inserts", file);
//     println("Experiment with 10 million inserts");
//     Vector.forEach(threads -> {
//         FileWrite.append(str = "\nThreads", file);
//         FileWrite.append(str = Int32.toString(threads), file);
//         FileWrite.append(str = "\n", file);
//         println("Threads");
//         println(threads);
//         FileWrite.append(str = Vector.toString(runWithThreadsRandom(rc, 20, threads, 10_000_000)), file)
//     }, Vector.range(1, 40))
// }

// def insertElementsDifferentOrder(): Unit \ IO + NonDet + Sys + FileWrite = region rc {
//     let file = "OrderExperiment.txt";
//     FileWrite.write(str = "", file);
//     FileWrite.append(str = "Experiment with varying order", file);
//     let nanoLimit = commonTimeLimitNano();
//     println("Experiment with different order:");
//     Vector.forEach(order -> Vector.forEach(insertNum -> 
//         Vector.forEach(threads -> {
//             FileWrite.append(str = "\nOrder:", file);
//             FileWrite.append(str = Int32.toString(order), file);
//             FileWrite.append(str = "\nInsertions:", file);
//             FileWrite.append(str = Int32.toString(insertNum), file);
//             FileWrite.append(str = "\nThreads:", file);
//             FileWrite.append(str = Int32.toString(threads), file);
//             FileWrite.append(str = "\n", file);
//             println("Order:");
//             println(order);
//             println("Insertions:");
//             println(insertNum);
//             println("Threads:");
//             println(threads);
//             FileWrite.append(str = Vector.toString(runWithThreadsRandomUntil(rc, testNum = repeatNum(), threadNum = threads, totalInserts = insertNum, nanoLimit, order)), file)
//         }, Vector#{1, 2, 5, 10, 20}), Vector#{10_000, 1_000_000}), Vector#{10, 20, 40, 60})
// }

// def insertFewElementsOften(): Unit \ IO + NonDet + Sys + FileWrite = region rc {
//     let file = "SmallStructures.txt";
//     FileWrite.write(str = "", file);
//     FileWrite.append(str = "Experiment with small depth", file);
//     println("Experiment with low height:");
//     let nanoLimit = commonTimeLimitNano();
//     Vector.forEach(insertNum -> 
//         Vector.forEach(threads -> {
//             FileWrite.append(str = "\nInsertions:", file);
//             FileWrite.append(str = Int32.toString(insertNum), file);
//             FileWrite.append(str = "\nThreads:", file);
//             FileWrite.append(str = Int32.toString(threads), file);
//             FileWrite.append(str = "\n", file);
//             println("Insertions:");
//             println(insertNum);
//             println("Threads:");
//             println(threads);
//             FileWrite.append(str = Vector.toString(runWithThreadsRandomUntil(rc, testNum = repeatNum(), threadNum = threads, totalInserts=insertNum, nanoLimit, standardOrder())), file)
//         }, Vector.range(1, 41)), 
//     Vector#{10_000, 1_000_000})
// }
