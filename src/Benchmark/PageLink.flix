mod PageLink {
    use Common.{loadTuplesFromFile, factFolder, unwrap, exit}

    pub def getFacts(): #{ PageLink(Int32, Int32), PageId(Int32, String) | r } \ IO + Sys = 
        let pagelinks = "${factFolder()}/pagelinks-100000.csv";
        let pageids = "${factFolder()}/page-ids.csv";
        let pagelinksTuples = loadTuplesFromFile(pagelinks, ",");
        let pageidsTuples = loadTuplesFromFile(pageids, ",");
        let map = Int32.fromString >> unwrap;
        let edges = pagelinksTuples |> List.map(x -> match x {
            case y :: _ :: w :: Nil => (map(y), map(w))
            case _ => exit("Error parsing facts file")
        });
        let ids = pageidsTuples |> List.map(x -> match x {
            case idStr :: _ :: title :: _ => (map(idStr), title)
            case _ => exit("Error parsing facts file")
        });
        let f1 = inject edges into PageLink;
        let f2 = inject ids into PageId;
        f1 <+> f2

    pub def runSingle(): Unit \ IO + Sys = 
        let f = getFacts();
        let r = #{
            ReachableId(x, y) :- PageLink(x, y).
            ReachableId(x, z) :- ReachableId(x, y), PageLink(y, z).
            Reachable(x, y) :- ReachableId(xId, yId), PageId(xId, x), PageId(yId, y).
        };
        query f, r select (x, y) from Reachable(x, y) |> Vector.length |> println

    pub def runWithFacts(f: #{ PageLink(Int32, Int32), PageId(Int32, String) }): Int64 \ IO + Clock = 
        let r = #{
            Reachable(x, y) :- PageLink(x, y).
            Reachable(x, z) :- Reachable(x, y), Reachable(y, z).
        };
        let x = query f, r select (x, y) from Reachable(x, y);
        let startTime = Clock.currentTime(TimeUnit.Nanoseconds);
        Common.forceEval(x);
        let endTime = Clock.currentTime(TimeUnit.Nanoseconds);
        endTime - startTime
}
