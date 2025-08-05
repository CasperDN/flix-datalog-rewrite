mod Path {
    use Common.{loadTuplesFromFile, getCwd, unwrap, exit}

    pub def getFacts(): #{ Edge(Int32, Int32) | s } \ IO + Sys =
        let filename = "${getCwd()}/src/Test/edge.csv";
        let tuples = loadTuplesFromFile(filename, ",");
        let map = Int32.fromString >> unwrap;
        let edges = tuples |> List.map(x -> match x {
            case y :: z :: Nil => (map(y), map(z))
            case _ => exit("Error parsing facts file")
        });
        println("Created facts");
        inject edges into Edge/2

    pub def runWithFacts(f: #{ Edge(Int32, Int32) }): Int64 \ IO + Clock =
        let r = #{
            Path(x, y) :- Edge(x, y).
            Path(x, z) :- Path(x, y), Path(y, z)
        };
        let x = query f, r select (x, y) from Path(x, y);
        let startTime = Clock.currentTime(TimeUnit.Nanoseconds);
        Common.forceEval(x);
        let endTime = Clock.currentTime(TimeUnit.Nanoseconds);
        endTime - startTime

}