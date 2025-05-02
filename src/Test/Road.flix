mod Road {
    import java.lang.System;
    use Common.{forceEval, unwrap}

    def getFacts(): #{ Road(Int64, Int64) | t } \ IO + Sys = 
        let path = "${Common.getCwd()}/data/roadNet-CA.txt";
        let tuples = Common.loadTuplesFromFile(path, 0, "\\s");
        let roads = List.take(10, tuples) |> 
            List.map(x -> match x{
                case src :: dst :: Nil => (unwrap(Int64.fromString(src)), unwrap(Int64.fromString(dst)))
                case _ => Common.exit("Error parsing facts file")
            });
        inject roads into Road

    pub def runTest(): Int64 \ IO + Sys + Clock = 
        let f = getFacts();
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