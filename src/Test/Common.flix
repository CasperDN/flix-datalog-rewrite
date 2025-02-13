mod Common {
    pub struct TestConfig[r] {
        program: String,
        timeout: Int64,
        runCount: Int8,
        verbose: Bool
    }

    pub def loadTuplesFromCSV(filename: String, del: String): List[List[String]] \ IO =
        let lines = match FileRead.handle(FileRead.readLines)(filename) {
            case Ok(v) => v
            case _ => ???
        };
        List.map(x -> String.split({ regex = del }, x), lines)
}



