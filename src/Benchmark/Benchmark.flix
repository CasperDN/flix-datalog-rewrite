use Common.{exit, unwrap}
import java.lang.System
def benchmark(): Unit \ {IO, Sys} =  
    let args: List[String] = Environment.handle(Environment.getArgs)();
    let programStr = match args {
        case program :: Nil => program
        case _ => exit("wrong program arguments")
    };
    benchmarkWithStr(programStr)

def benchmarkWithStr(programStr: String): Unit \ {IO, Sys} = match programStr {
    case "All" =>
        Vector#{"Road", "PageLink", "RoadShuffled", "PageLinkShuffled"} |>
        Vector.forEach(benchmarkRun)
    case _ => benchmarkRun(programStr)
}

def benchmarkRun(programStr: String): Unit \ {IO, Sys} =
    // We cant unify the SchemaRow types so we write the facts out individually
    let roadFacts = if (programStr == "Road" or programStr == "RoadShuffled" or programStr == "RoadLattice") Road.getFacts() else #{ };
    let pageLinkFacts = if (programStr == "PageLink" or programStr == "PageLinkShuffled") PageLink.getFacts() else #{ };
    // let pathFacts = if (programStr == "Path") Path.getFacts() else #{ };
    let runCount: Int32 = 5;
    println("Program: ${programStr}");
    let range = List.range(0, runCount) |> List.map(Int32.toInt64);
    let sumTime: Int64 = List.foldLeft(_ -> acc -> {
        System.gc();
        match programStr {
        case "Road" => acc + Clock.handle(Road.runWithFacts)(roadFacts)
        case "RoadShuffled" => acc + Clock.handle(Road.runWithFactsShuffled)(roadFacts)
        case "RoadLattice" => acc + Clock.handle(Road.runLatticeWithFacts)(roadFacts)
        case "PageLink" => acc + Clock.handle(PageLink.runWithFacts)(pageLinkFacts)
        case "PageLinkShuffled" => acc + Clock.handle(PageLink.runWithFactsShuffled)(pageLinkFacts)
        // case "Path" => acc + Clock.handle(Path.runWithFacts)(pathFacts)
        case _ => exit("No such program")
    }}, 0i64, range);
    let avgTime = sumTime / Int32.toInt64(runCount);
    prettyPrintTime(avgTime)

def numDigits(x: Int64): Int32 = String.length(Int64.toString(x))

def prettyPrintTime(avgTime: Int64): Unit \ IO = 
    let maxDigits = numDigits(avgTime);
    let avgTimeS = avgTime / 1000i64;
    println("avg time:");
    println("${avgTime} ms");
    println(String.padLeft(maxDigits + 2, ' ', "${avgTimeS} s"))