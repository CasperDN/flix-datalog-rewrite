mod Path {
    import java.lang.System;

    def getFacts(): #{ Edge(Int32, Int32) | r } \ {IO, Sys} = 
        let path = "${Common.getCwd()}/src/Test/edge.csv";
        let tuples = Common.loadTuplesFromCSV(path, " ");
        let map = x -> match Int32.fromString(x) {
            case Some(y) => y
            case None => ???
        };
        let edges = List.map(x -> match x {
            case y :: z :: Nil => (map(y), map(z))
            case _ => ???
        }, tuples);
        inject edges into Edge

    pub def path(): Int64 \ {IO, Sys} = 
        let f = getFacts();
        let r = #{
            Path(x, y) :- Edge(x, y).
            Path(x, z) :- Path(x, y), Path(y, z)
        };
        let startTime = System.nanoTime();
        let x = Vector.find(_ -> true, query f, r select (x, y) from Path(x, y));
        let endTime = System.nanoTime();
        println(x);
        endTime - startTime
}
