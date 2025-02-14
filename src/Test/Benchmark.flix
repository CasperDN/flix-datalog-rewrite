def main3(): Unit \ {IO, Sys} =  
    let _programs = Map#{
        "Path" => Path.path,
        "Titanic" => Titanic.titanic
    };
    // // Rudimentary argparsing. Can be developed further later.
    // let args: List[String] = Environment.handle(Environment.getArgs)();
    // let progToTest = match args {
    //     case prog :: Nil => Map.get(prog, programs)
    //     case _ => 
    //         println("wrong program arguments");
    //         ???
    // };
    let progToTest = Some(Path.path);
    let runCount: Int32 = 1;
    match progToTest {
        case Some(program) =>   
            let range = List.map(Int32.toInt64, List.range(0, runCount));
            let sumTime: Int64 = List.foldLeft(_ -> acc -> acc + program(), 0i64, range);
            let avgTime = sumTime / Int32.toInt64(runCount);
            println(avgTime)
        case _ => println("No such program")
    }
    

