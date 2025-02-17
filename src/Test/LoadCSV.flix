pub def loadTuplesFromCSV(filename: String, del: String): List[List[String]] \ IO =
    let lines = match FileRead.handle(FileRead.readLines)(filename) {
        case Ok(v) => v
        case _ => ???
    };
    List.map(x -> String.split({ regex = del }, x), lines)
