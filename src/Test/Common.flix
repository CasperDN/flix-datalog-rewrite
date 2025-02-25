mod Common {

    pub def loadTuplesFromFile(filename: String, skip: Int32, del: String): List[List[String]] \ {IO, Sys} =
        let func = _ -> {
            if (not FileRead.exists(filename)) 
                exit("No such file: ${filename}")
            else ();
            let lines = FileRead.readLines(filename);
            List.map(
                x -> String.split({ regex = del }, x), 
                List.slice({start = skip}, {end = List.size(lines)}, lines)
            )
        };
        match FileRead.handle(func)() {
            case Ok(v) => v
            case _ => ???
        } 
    
    pub def unwrap(opt: Option[t]): t = match opt {
        case Some(v) => v
        case None => bug!("Could not unwrap option")
    }

    pub def forceEval(x: Bool): Unit \ IO = 
        if (x) { 
            if (not x) println()
            else ()
        } else ()

    pub def getCwd(): String \ {IO, Sys} = match Environment.handle(Environment.getCurrentWorkingDirectory)() {
        case Some(cwd) => cwd
        case None => exit("Could not get current working directory")
    }

    pub def exit(str: String): a \ {IO, Sys} = 
        println(str);
        Exit.handle(Exit.exit)(1) 
    
}



