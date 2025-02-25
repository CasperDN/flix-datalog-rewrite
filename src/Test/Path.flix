mod Path {
    import java.lang.System;

    def getFacts(): #{ Edge(Int32, Int32) | r } \ {IO, Sys} = 
        let path = "${Common.getCwd()}/edge.csv";
        let tuples = Common.loadTuplesFromFile(path, 0, " ");
        let map = x -> match Int32.fromString(x) {
            case Some(y) => y
            case None => ???
        };
        let edges = List.map(x -> match x {
            case y :: z :: Nil => (map(y), map(z))
            case _ => ???
        }, tuples);
        inject edges into Edge

    pub def runTest(): Int64 \ {IO, Sys} = 
        let f = getFacts();
        let r = #{
            Path(x, y) :- Edge(x, y).
            Path(x, z) :- Path(x, y), Path(y, z)
        };
        let x = query f, r select (x, y) from Path(x, y) |> Vector.exists(_ -> true);
        let startTime = System.nanoTime();
        Common.forceEval(x);
        let endTime = System.nanoTime();
        endTime - startTime
}
