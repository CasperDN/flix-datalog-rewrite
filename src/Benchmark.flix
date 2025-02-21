use Common.exit
def benchmark(): Unit \ {IO, Sys} =  
    let programs = Map#{
        "Path" => Path.runTest,
        "Titanic" => Titanic.runTest
    };
    let args: List[String] = Environment.handle(Environment.getArgs)();
    let programStr = match args {
        case program :: Nil => program
        case _ => exit("wrong program arguments")
    };
    let program = match Map.get(programStr, programs) {
        case Some(x) => x
        case _ => exit("Invalid program: ${programStr}")
    };
    let runCount: Int32 = 1;
    let range = List.map(Int32.toInt64, List.range(0, runCount));
    let sumTime: Int64 = List.foldLeft(_ -> acc -> acc + program(), 0i64, range);
    let avgTime = sumTime / Int32.toInt64(runCount);
    println("Program ${programStr}");
    prettyPrintTime(avgTime)
    
def numDigits(x: Int64): Int32 = String.length(Int64.toString(x))

def prettyPrintTime(avgTime: Int64): Unit \ IO = 
    let maxDigits = numDigits(avgTime);
    let avgTimeMs = avgTime / 1000000i64;
    let avgTimeS = avgTimeMs / 1000i64;
    println("avg time:");
    println("${avgTime} ns");
    println(String.padLeft(maxDigits + 3, ' ', "${avgTimeMs} ms"));
    println(String.padLeft(maxDigits + 2, ' ', "${avgTimeS} s"))