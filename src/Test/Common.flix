mod Common {
    pub def loadTuplesFromCSV(filename: String, del: String): List[List[String]] \ IO =
        println(filename);
        let lines = match FileRead.handle(FileRead.readLines)(filename) {
            case Ok(v) => v
            case _ => ???
        };
        List.map(x -> String.split({ regex = del }, x), lines)

    pub def getCwd(): String \ {IO, Sys} = match Environment.handle(Environment.getCurrentWorkingDirectory)() {
        case Some(cwd) => cwd
        case None => println("Could not get cwd"); ???
}
}



