mod Road {
    import java.lang.System;
    use Common.{forceEval, unwrap, loadTuplesFromFile, factFolder, exit}

    pub def getFacts(): #{ Road(Int64, Int64) | t } \ {IO, Sys} = 
        let path = "${factFolder()}/road-2000000.csv";
        let tuples = loadTuplesFromFile(path, ",");
        let map = Int64.fromString >> unwrap;
        let roads = tuples |> List.map(x -> match x {
            case src :: dst :: Nil => (map(src), map(dst))
            case _ => exit("Error parsing facts file")
        });
        inject roads into Road

    pub def runSingle(): Unit \ IO + Sys = Clock.runWithIO(() -> {
        let f = getFacts();
        let r = #{
            Path(x, y) :- Road(x, y).
            Path(x, z) :- Road(y, z), Path(x, y).
        };
        let startTime = Clock.currentTime(TimeUnit.Nanoseconds);
        let x = query f, r select (x, y) from Path(x, y);
        Common.forceEval(x);
        let endTime = Clock.currentTime(TimeUnit.Nanoseconds);
        println(endTime - startTime)
    })

    pub def runWithFacts(f: #{ Road(Int64, Int64) }): Int64 \ IO + Clock = 
        let r = #{
            Path(x, y) :- Road(x, y).
            Path(x, z) :- Path(x, y), Road(y, z).
        };
        let x = query f, r select (x, y) from Path(x, y);
        let startTime = Clock.currentTime(TimeUnit.Nanoseconds);
        Common.forceEval(x);
        let endTime = Clock.currentTime(TimeUnit.Nanoseconds);
        endTime - startTime

    pub def runLatticeWithFacts(f: #{ Road(Int64, Int64) }): Int64 \ IO + Clock = 
        let r = #{
            Path(x, y; Down.Down(1)) :- Road(x, y).
            Path(x, z; l1 + Down.Down(1)) :- Path(x, y; l1), Road(y, z).
        };
        let x = query f, r select shortest from Path(x, y; shortest);
        let startTime = Clock.currentTime(TimeUnit.Nanoseconds);
        Common.forceEval(x);
        let endTime = Clock.currentTime(TimeUnit.Nanoseconds);
        endTime - startTime
}