mod PageLink {
    use Common.{loadTuplesFromFile, factFolder, unwrap, exit}

    pub def getFacts(): #{ PageLink(Int32, Int32), PageId(Int32, String), Stub(Int32, String) | r } \ IO + Sys = 
        let pagelinks = "${factFolder()}/pagelinks-100000.csv";
        let pageids = "${factFolder()}/page-ids.csv";
        let stubsFile = "${factFolder()}/stubs.csv";
        let pagelinksTuples = loadTuplesFromFile(pagelinks, ",");
        let pageidsTuples = loadTuplesFromFile(pageids, ",");
        let stubFromFile = loadTuplesFromFile(stubsFile, ",");
        let map = Int32.fromString >> unwrap;
        let edges = pagelinksTuples |> List.map(x -> match x {
            case y :: _ :: w :: Nil => (map(y), map(w))
            case _ => exit("Error parsing facts file")
        });
        let ids = pageidsTuples |> List.map(x -> match x {
            case idStr :: _ :: title :: _ => (map(idStr), title)
            case _ => exit("Error parsing facts file")
        });
        let stubTuples = stubFromFile |> List.map(x -> match x {
            case idStr :: title :: Nil => (map(idStr), title)
            case _ => exit("Error parsing facts file")
        });
        let f1 = inject edges into PageLink;
        let f2 = inject ids into PageId;
        let f3 = inject stubTuples into Stub;
        f1 <+> f2 <+> f3

    pub def runSingle(): Unit \ IO + Sys = 
        let f = getFacts();
        let r = #{
            Leq("autoconfirmed", "autoconfirmed").
            Leq("autoconfirmed", "extendedconfirmed").
            Leq("autoconfirmed", "sysop").
            Leq("extendedconfirmed", "extendedconfirmed").
            Leq("extendedconfirmed", "sysop").
            Leq("sysop", "sysop").
            Leq("templateeditor", "sysop").

            ProtectedId(x) :- Protected(x, _).

            ProtectedExtended(x, "None") :- PageId(x, _), not ProtectedId(x).

            LeqLinks(x, y) :- PageLink(x, y), not ProtectedId(x).
            LeqLinks(x, y) :- PageLink(x, y).

            PageLinkStub(x, y) :- PageLink(x, y), StubId(x), StubId(y).
            ReachableStub(x, y) :- PageLinkStub(x, y).
            ReachableStub(x, z) :- ReachableStub(x, y), PageLinkStub(y, z).
            Reachable(x, y) :- ReachableStub(xId, yId), PageId(xId, x), PageId(yId, y).

            PageLinkNonStub(x, y) :- PageLink(x, y), not StubId(x), not StubId(y).
            ReachableNonStub(x, y) :- PageLinkNonStub(x, y).
            ReachableNonStub(x, z) :- ReachableNonStub(x, y), PageLinkNonStub(y, z).
            Reachable(x, y) :- ReachableNonStub(xId, yId), PageId(xId, x), PageId(yId, y).
        };
        query f, r select (x, y) from Reachable(x, y) |> Vector.length |> println

    pub def runWithFacts(f: #{ PageLink(Int32, Int32), PageId(Int32, String), Stub(Int32, String) }): Int64 \ IO + Clock = 
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
