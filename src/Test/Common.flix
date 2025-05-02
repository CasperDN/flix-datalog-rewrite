mod Common {

    pub def loadTuplesFromFile(filename: String, max: Int32, del: String): List[List[String]] \ {IO, Sys} =
        let func = _ -> {
            if (not FileRead.exists(filename)) 
                exit("No such file: ${filename}")
            else ();
            let lines = FileRead.readLines(filename);
            List.slice(start = 0, end = List.size(lines) `Int32.min` max, lines) |> 
            List.map(x -> String.split(regex = del, x))
        };
        match FileRead.handle(func)() {
            case Ok(v) => v
            case _ => ???
        }
    
    pub def unwrap(opt: Option[t]): t = match opt {
        case Some(v) => v
        case None => bug!("Could not unwrap option")
    }

    pub def forceEval(x: Vector[a]): Unit \ IO = 
        if (Vector.length(x) == -1)
            println()
        else ()

    pub def getCwd(): String \ {IO, Sys} = match Environment.handle(Environment.getCurrentWorkingDirectory)() {
        case Some(cwd) => cwd
        case None => exit("Could not get current working directory")
    }

    pub def exit(str: String): a \ {IO, Sys} = 
        println(str);
        Exit.handle(Exit.exit)(1) 
    
}