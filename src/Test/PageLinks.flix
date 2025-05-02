mod PageLinks    {
    def getFacts(): #{ PageLink(Int32, Int32), PageId(Int32, String) | r } \ IO + Sys = region rc {
        let pagelinks = "${Common.getCwd()}/data/wikipedia/pagelinks.csv";
        let pageids = "${Common.getCwd()}/data/wikipedia/page-ids.csv";
        let pagelinksTuples = Common.loadTuplesFromFile(pagelinks, 1000, ",");
        let pageidsTuples = Common.loadTuplesFromFile(pageids, Int32.maxValue(), ",");
        let map = x -> match Int32.fromString(x) {
            case Some(y) => y
            case None => ???
        };
        let edges = pagelinksTuples |> List.map(x -> match x {
            case y :: _ :: w :: Nil => (map(y), map(w))
            case _ => println(x); ???
        });
        let ids = pageidsTuples |> List.map(x -> match x {
            case idStr :: _ :: title :: xs => (map(idStr), title)
            case _ => ???
        });
        let f1 = inject edges into PageLink;
        let f2 = inject ids into PageId;
        println("Created facts");
        f1 <+> f2
    }

    pub def runSingle(): Unit \ IO + Sys = 
        let f = getFacts();
        let r = #{
            ReachableId(x, y) :- PageLink(x, y).
            ReachableId(x, z) :- ReachableId(x, y), PageLink(y, z).
            Reachable(x, y) :- ReachableId(xId, yId), PageId(xId, x), PageId(yId, y).
        };
        query f, r select (x, y) from Reachable(x, y) |> println

    // pub def runTest(): Int64 \ IO + Sys + Clock = 
    //     let f = getFacts();
    //     let r = #{
    //         Reachable(x, y) :- PageLink(x, y).
    //         Reachable(x, z) :- Reachable(x, y), Reachable(y, z).
    //     };
    //     let startTime = Clock.currentTime(TimeUnit.Nanoseconds);
    //     let x = query f, r select (x, y) from Reachable(x, y);
    //     println(x |> Vector.length);
    //     Common.forceEval(x);
    //     let endTime = Clock.currentTime(TimeUnit.Nanoseconds);
    //     endTime - startTime
}
