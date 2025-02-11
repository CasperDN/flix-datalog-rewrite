def getEdges(): #{ Edge(Int32, Int32) | s } \ IO = 
    let tuples = loadTuplesFromCSV("C:/Users/adamt/Desktop/Datalogi/flix-datalog-rewrite/src/Test/edge.csv", " ");
    let map = x -> match Int32.fromString(x) {
        case Some(y) => y
        case None => ???
    };
    let edges = List.map(x -> match x {
        case y :: z :: Nil => (map(y), map(z))
        case _ => ???
    }, tuples);
    inject edges into Edge

def main2(): Unit \ { IO } = 
    let r = #{
        Path(x, y) :- Edge(x, y).
        Path(x, z) :- Path(x, y), Path(y, z)
    };
    let x = Vector.length(query getEdges(), r select (x, y) from Path(x, y));
    println(x)