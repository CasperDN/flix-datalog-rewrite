use Common.exit
def benchmark(): Unit \ {IO, Sys} =  
    let programs = Map#{
        "Path" => Path.runTest,
        "Titanic" => Titanic.runTest
    };
    // // Rudimentary argparsing. Can be developed further later.
    let args: List[String] = Environment.handle(Environment.getArgs)();
    let program = match args {
        case program :: Nil => match Map.get(program, programs) {
            case Some(x) => x
            case _ => exit("Invalid program: ${program}", 2)
        }
        case _ => exit("wrong program arguments", 1)
    };
    let runCount: Int32 = 1;
    let range = List.map(Int32.toInt64, List.range(0, runCount));
    let sumTime: Int64 = List.foldLeft(_ -> acc -> acc + program(), 0i64, range);
    let avgTime = sumTime / Int32.toInt64(runCount);
    println("avg time: ${avgTime} ns")
    

