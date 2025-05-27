use Common.{exit, unwrap}

def benchmark(): Unit \ {IO, Sys} =  
    let args: List[String] = Environment.handle(Environment.getArgs)();
    let programStr = match args {
        case program :: Nil => program
        case _ => exit("wrong program arguments")
    };
    benchmarkWithStr(programStr)

def benchmarkWithStr(programStr: String): Unit \ {IO, Sys} = match programStr {
    case "All" =>
        Vector#{"Road", "RoadLattice", "PageLink", "Path"} |>
        Vector.forEach(benchmarkRun)
    case _ => benchmarkRun(programStr)
}

def benchmarkRun(programStr: String): Unit \ {IO, Sys} =
    // We cant unify the SchemaRow types so we write the facts out individually
    let roadFacts = if (programStr == "Road" or programStr == "RoadLattice") Road.getFacts() else #{ };
    let pageLinkFacts = if (programStr == "PageLink") PageLink.getFacts() else #{ };
    let pathFacts = if (programStr == "Path") Path.getFacts() else #{ };
    let runCount: Int32 = 1;
    let range = List.range(0, runCount) |> List.map(Int32.toInt64);
    let sumTime: Int64 = List.foldLeft(_ -> acc -> match programStr {
        case "Road" => acc + Clock.handle(Road.runWithFacts)(roadFacts)
        case "RoadLattice" => acc + Clock.handle(Road.runLatticeWithFacts)(roadFacts)
        case "PageLink" => acc + Clock.handle(PageLink.runWithFacts)(pageLinkFacts)
        case "Path" => acc + Clock.handle(Path.runWithFacts)(pathFacts)
        case _ => exit("No such program")
    }, 0i64, range);
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