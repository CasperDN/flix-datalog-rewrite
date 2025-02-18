mod Common {
    use Exit.exit

    pub def loadTuplesFromCSV(filename: String, del: String): List[List[String]] \ IO =
        let func = _ -> {
            if (not FileRead.exists(filename)) 
                bug!("No such file: ${filename}")
            else ();
            let lines = FileRead.readLines(filename);
            List.map(x -> String.split({ regex = del }, x), lines)
        };
        match FileRead.handle(func)() {
            case Ok(v) => v
            case _ => ???
        } 
    
    pub def forceEval(x: Bool): Unit \ IO = 
        if (x) { 
            if (not x) println()
            else ()
        } else ()

    pub def getCwd(): String \ {IO, Sys} = match Environment.handle(Environment.getCurrentWorkingDirectory)() {
        case Some(cwd) => cwd
        case None => bug!("Could not get current working directory")
    }

    pub def exit(str: String, exitCode: Int32): a \ {IO, Sys} = 
        println(str);
        Exit.handle(exit)(exitCode) 
    
}



