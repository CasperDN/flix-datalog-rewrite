mod PageLink {
    use Common.{loadTuplesFromFile, factFolder, unwrap, exit}

    pub def getFacts(): #{ PageLink(Int32, Int32), PageId(Int32, String), Protected(Int32, String), Leq(String, String) | r } \ IO + Sys = 
        let pagelinks = "${factFolder()}/pagelinks-1000000.csv";
        let pageids = "${factFolder()}/page-ids.csv";
        let protectedFile = "${factFolder()}/restrictions.csv";
        let leqFile = "${factFolder()}/wiki-leq.csv";
        let pagelinksTuples = loadTuplesFromFile(pagelinks, ",");
        let pageidsTuples = loadTuplesFromFile(pageids, ",");
        let restrictionsFromFile = loadTuplesFromFile(protectedFile, ",");
        let leqFromFile = loadTuplesFromFile(leqFile, ",");
        let map = Int32.fromString >> unwrap;
        let edges = pagelinksTuples |> List.map(x -> match x {
            case y :: _ :: w :: Nil => (map(y), map(w))
            case _ => exit("Error parsing facts file")
        });
        let ids = pageidsTuples |> List.map(x -> match x {
            case idStr :: _ :: title :: _ => (map(idStr), title)
            case _ => exit("Error parsing facts file")
        });
        let restrictedTuples = restrictionsFromFile |> List.map(x -> match x {
            case idStr :: title :: Nil => (map(idStr), title)
            case _ => exit("Error parsing facts file")
        });
        let leqTuples = leqFromFile |> List.map(x -> match x {
            case small :: big :: Nil => (small, big)
            case _ => exit("Error parsing facts file")
        });
        let f1 = inject edges into PageLink;
        let f2 = inject ids into PageId;
        let f3 = inject restrictedTuples into Protected;
        let f4 = inject leqTuples into Leq;
        f1 <+> f2 <+> f3 <+> f4


    pub def getSmallFacts(): #{ PageLink(Int32, Int32), PageId(Int32, String), Protected(Int32, String), Leq(String, String) | r } \ IO + Sys = 
        let pagelinks = "${factFolder()}/pagelinks-1000000.csv";
        let pageids = "${factFolder()}/page-ids.csv";
        let protectedFile = "${factFolder()}/restrictions.csv";
        let leqFile = "${factFolder()}/wiki-leq.csv";
        let pagelinksTuples = loadTuplesFromFile(pagelinks, ",");
        let pageidsTuples = loadTuplesFromFile(pageids, ",");
        let restrictionsFromFile = loadTuplesFromFile(protectedFile, ",");
        let leqFromFile = loadTuplesFromFile(leqFile, ",");
        let map = Int32.fromString >> unwrap;
        let edges = pagelinksTuples |> List.map(x -> match x {
            case y :: _ :: w :: Nil => (map(y), map(w))
            case _ => exit("Error parsing facts file")
        });
        let ids = pageidsTuples |> List.map(x -> match x {
            case idStr :: _ :: title :: _ => (map(idStr), title)
            case _ => exit("Error parsing facts file")
        });
        let restrictedTuples = restrictionsFromFile |> List.map(x -> match x {
            case idStr :: title :: Nil => (map(idStr), title)
            case _ => exit("Error parsing facts file")
        });
        let leqTuples = leqFromFile |> List.map(x -> match x {
            case small :: big :: Nil => (small, big)
            case _ => exit("Error parsing facts file")
        });
        let f1 = inject edges into PageLink;
        let f2 = inject ids into PageId;
        let f3 = inject restrictedTuples into Protected;
        let f4 = inject leqTuples into Leq;
        f1 <+> f2 <+> f3 <+> f4

    pub def runSingle(): Unit \ IO + Sys = 
        let f = getFacts();
        let r = #{
            ProtectedId(x) :- Protected(x, _).

            RealPageLink(x, y) :- PageLink(x, y), PageId(x, _), PageId(y, _).

            ReachableId(x, y) :- RealPageLink(x, y), not ProtectedId(x).
            ReachableId(x, y) :- RealPageLink(x, y), Protected(x, xPro), Protected(y, yPro), Leq(xPro, yPro).

            ReachableId(x, z) :- ReachableId(x, y), RealPageLink(y, z), not ProtectedId(x).
            ReachableId(x, z) :- ReachableId(x, y), RealPageLink(y, z), Protected(x, xPro), Protected(z, zPro), Leq(xPro, zPro).
            Reachable(x, y) :- ReachableId(xId, yId), PageId(xId, x), PageId(yId, y).
        };
        query f, r select (x, y) from Reachable(x, y) |> Vector.length |> println

    pub def runWithFacts(f: #{ PageLink(Int32, Int32), PageId(Int32, String), Protected(Int32, String), Leq(String, String) }): Int64 \ IO + Clock = 
        let r = #{
            ProtectedId(x) :- Protected(x, _).

            RealPageLink(x, y) :- PageLink(x, y), PageId(x, _), PageId(y, _).

            ReachableId(x, y) :- RealPageLink(x, y), not ProtectedId(x).
            ReachableId(x, y) :- RealPageLink(x, y), Protected(x, xPro), Protected(y, yPro), Leq(xPro, yPro).

            ReachableId(x, z) :- ReachableId(x, y), RealPageLink(y, z), not ProtectedId(x).
            ReachableId(x, z) :- ReachableId(x, y), RealPageLink(y, z), Protected(x, xPro), Protected(z, zPro), Leq(xPro, zPro).
            Reachable(x, y) :- ReachableId(xId, yId), PageId(xId, x), PageId(yId, y).
        };
        let x = query f, r select (x, y) from Reachable(x, y);
        let startTime = Clock.now();
        println("Start: ${startTime}");
        Common.forceEval(x);
        let endTime = Clock.now();
        endTime - startTime

    pub def runWithFactsShuffled(f: #{ PageLink(Int32, Int32), PageId(Int32, String), Protected(Int32, String), Leq(String, String) }): Int64 \ IO + Clock = 
        let r = #{
            ProtectedId(x) :- Protected(x, _).

            RealPageLink(x, y) :- PageId(x, _), PageLink(x, y), PageId(y, _).

            ReachableId(x, y) :- RealPageLink(x, y), not ProtectedId(x).
            ReachableId(x, y) :- Leq(xPro, yPro), Protected(x, xPro), Protected(y, yPro), RealPageLink(x, y).

            ReachableId(x, z) :- ReachableId(x, y), RealPageLink(y, z), not ProtectedId(x).
            ReachableId(x, z) :- ReachableId(x, y), RealPageLink(y, z), Protected(x, xPro), Protected(z, zPro), Leq(xPro, zPro).
            Reachable(x, y) :- ReachableId(xId, yId), PageId(xId, x), PageId(yId, y).
        };
        let x = query f, r select (x, y) from Reachable(x, y);
        let startTime = Clock.now();
        println("Start: ${startTime}");
        Common.forceEval(x);
        let endTime = Clock.now();
        endTime - startTime


}
