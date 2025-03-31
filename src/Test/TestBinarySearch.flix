def binSOuterIfNoThreeWay(key: v, length: Int32, arr: Array[v, r]): Int32 \ r with Order[v] =
    if (length == 0)
        -1
    else
        def f(l: Int32, r: Int32): Int32 \ r = {
            if (l <= r) {
                let m = (l + r) `Int32.rightShift` 1;
                let elem = Array.get(m, arr);
                if (elem < key) f(m+1, r)
                else if (elem > key) f(l, m-1)
                else m
            } else -l-1
        };
        f(0, length - 1)

def binSNoOuterIfNoThreeWay(key: v, length: Int32, arr: Array[v, r]): Int32 \ r with Order[v] =
    def f(l: Int32, r: Int32): Int32 \ r = {
        if (l <= r) {
            let m = (l + r) `Int32.rightShift` 1;
            let elem = Array.get(m, arr);
            if (elem < key) f(m+1, r)
            else if (elem > key) f(l, m-1)
            else m
        } else -l-1
    };
    f(0, length - 1)

def binSOuterIfThreeWay(key: v, length: Int32, arr: Array[v, r]): Int32 \ r with Order[v] =
    if (length == 0)
        -1
    else
        def f(l: Int32, r: Int32): Int32 \ r = {
            if (l <= r) {
                let m = (l + r) `Int32.rightShift` 1;
                match Array.get(m, arr) <=> key {
                    case Comparison.LessThan => f(m + 1, r)
                    case Comparison.GreaterThan => f(l, m - 1)
                    case Comparison.EqualTo => m
                }
            } else -l-1
        };
        f(0, length - 1)

def binSNoOuterIfThreeWay(key: v, length: Int32, arr: Array[v, r]): Int32 \ r with Order[v] =
    def f(l: Int32, r: Int32): Int32 \ r = {
        if (l <= r) {
            let m = (l + r) `Int32.rightShift` 1;
            match Array.get(m, arr) <=> key {
                case Comparison.LessThan => f(m + 1, r)
                case Comparison.GreaterThan => f(l, m - 1)
                case Comparison.EqualTo => m
            }
        } else -l-1
    };
    f(0, length - 1)

def mainBinarySearch(): Unit \ IO + NonDet + Sys = {
    let _ = FileWrite.runWithIO(() ->{
    binarySearchExperiment();
    ()}); 
    ()
}

def binarySearchExperiment(): Unit \ IO + NonDet + Sys + FileWrite = {
    let reads = readNum();
    let file = "binaryRead1.txt";
    FileWrite.write(str = "", file);
    let nanoLimit = commonTimeLimitNano();
    FileWrite.append(str = "Binary: Read experiment", file);
    FileWrite.append(str = "\nTotal reads: ${reads}", file);
    println("Binary: Read experiment");
    region rc {
        Vector.forEach(match (name, binarySearch) ->
            Vector.forEach(inserts -> {
                FileWrite.append(str = "\n", file);
                FileWrite.append(str = name, file);
                FileWrite.append(str = "\nInserts: ", file);
                FileWrite.append(str = Int32.toString(inserts), file);
                FileWrite.append(str = "\n", file);
                println("Inserts");
                println(inserts);
                FileWrite.append(
                    str = Vector.toString(
                        Random.runWithIO(() -> runBinaryRead(
                            testNum = repeatNum(), 
                            totalInserts = inserts, 
                            generatedReads = reads, 
                            nanoLimit, 
                            binarySearch, 
                            rc
                        ))), 
                    file)
            }, Vector#{10_000, 100_000, 1_000_000}), 
        Vector#{
            ("No Outer, No ThreeWay", binSNoOuterIfNoThreeWay), 
            ("No Outer, ThreeWay", binSNoOuterIfThreeWay), 
            ("Outer, No ThreeWay", binSOuterIfNoThreeWay), 
            ("Outer, ThreeWay", binSOuterIfThreeWay)})
    }
}

def runBinaryRead(
    testNum: {testNum = Int32}, 
    totalInserts: {totalInserts = Int32}, 
    generatedReads: {generatedReads = Int32}, 
    timeLimit: Int64, binarySearch: Int64 -> Int32 -> Array[Int64, r] -> Int32 \ r,
    rc: Region[r]
): Vector[Int64] \ IO + Random + Sys + r =
    let arr = List.toArray(rc, List.sort(List.map(_ -> (Random.randomInt64()), List.range(0, totalInserts#totalInserts))));
    let searches = List.map(_ -> (Random.randomInt64()), List.range(0, generatedReads#generatedReads));
    runNTestsGeneral(testNum#testNum, () -> readUntilBinaryRead(arr, searches, timeLimit, binarySearch))

def readUntilBinaryRead(arr: Array[Int64, r], toRead: List[Int64], timeLimit: Int64, binarySearch: Int64 -> Int32 -> Array[Int64, r] -> Int32 \ r): Int64 \ IO = 
    let readNum = Array.size(arr);
    Int32.toInt64(readNum) * Clock.runWithIO(() -> {
        let start = Clock.currentTime(TimeUnit.Nanoseconds);
        let timeFunc = () -> Clock.runWithIO(() -> Clock.currentTime(TimeUnit.Nanoseconds)) - start > timeLimit;
        let readFunc: (Unit -> Unit \ IO) = () -> region rc2 {
                spawn unchecked_cast(() -> {
                    List.forEach(p -> {
                        binarySearch(p, readNum, arr);
                        ()
                    }, toRead)} as Unit -> Unit \ IO)() @ rc2
        };
        repeatUntil(readFunc, timeFunc)
    })