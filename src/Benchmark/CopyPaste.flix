mod CopyPaste {
    import java.lang.System;
    use Common.{forceEval, unwrap, loadTuplesFromFile, factFolder, exit}

    def n(): Int32 = 5000


    pub def getFacts(): #{ A(Int32) | t } = 
        inject List.range(0, n()) into A

    pub def runSingle(): Unit \ IO = Clock.runWithIO(() -> {
        let f = getFacts();
        let r = #{
            Res(x, y, z, w) :- A(x), A(y), A(z), A(w).
        };
        let startTime = Clock.now();
        let x = query f, r select (x, y, z, w) from Res(x, y, z, w);
        Common.forceEval(x);
        let endTime = Clock.now();
        println(endTime - startTime)
    })

    pub def runWithFacts(f: #{ A(Int64) }): Int64 \ IO + Clock = 
        let r = #{
            Res(x, y, z, w) :- A(x), A(y), A(z), A(w).
        };
        let x = query f, r select (x, y, z, w) from Res(x, y, z, w);
        let startTime = Clock.now();
        Common.forceEval(x);
        let endTime = Clock.now();
        endTime - startTime
}