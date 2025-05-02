use Common.exit
def benchmark(): Unit \ {IO, Sys} =  
    let programs = Map#{
        "Road" => Road.runTest
        // "PageLinks" => PageLinks.runTest
    };
    // let args: List[String] = Environment.handle(Environment.getArgs)();
    // let _programStr = match args {
    //     case program :: Nil => program
    //     case _ => exit("wrong program arguments")
    // };
    let programStr = "PageLinks";
    let program = match Map.get(programStr, programs) {
        case Some(x) => Clock.handle(x)
        case _ => exit("Invalid program: ${programStr}")
    };
    let runCount: Int32 = 1;
    let range = List.map(Int32.toInt64, List.range(0, runCount));
    let sumTime: Int64 = List.foldLeft(_ -> acc -> acc + program(), 0i64, range);
    let avgTime = sumTime / Int32.toInt64(runCount);
    println("Program: ${programStr}");
    prettyPrintTime(avgTime)
    
def numDigits(x: Int64): Int32 = String.length(Int64.toString(x))

def prettyPrintTime(avgTime: Int64): Unit \ IO = 
    let maxDigits = numDigits(avgTime);
    let avgTimeUs = avgTime / 1000i64;
    let avgTimeMs = avgTimeUs / 1000i64;
    let avgTimeS = avgTimeMs / 1000i64;
    println("avg time:");
    println("${avgTime} ns");
    println(String.padLeft(maxDigits + 3, ' ', "${avgTimeUs} µs"));
    println(String.padLeft(maxDigits + 3, ' ', "${avgTimeMs} ms"));
    println(String.padLeft(maxDigits + 2, ' ', "${avgTimeS} s"))