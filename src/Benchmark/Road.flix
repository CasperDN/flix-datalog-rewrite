mod Road {
    import java.lang.System;
    use Common.{forceEval, unwrap, loadTuplesFromFile, factFolder, exit}

    use Path.{Path, Bot};

    pub enum Path[a] with ToString {
        case Path(List[a], Int32)
        case Bot // Infinitely long path
    }

    instance Eq[Path[a]] {
        pub def eq(x: Path[a], y: Path[a]): Bool = match (x, y) {
            case (Bot, Bot)                 => true
            case (Path(_, l1), Path(_, l2)) => l1 == l2
            case _                          => false
        }
    }

    instance Order[Path[a]] with Order[a] {
        pub def compare(x: Path[a], y: Path[a]): Comparison = match (x, y) {
            case (Bot, Bot)                 => Comparison.EqualTo
            case (Bot, _)                   => Comparison.LessThan
            case (_, Bot)                   => Comparison.GreaterThan
            case (Path(list1, l1), Path(list2, l2)) => 
                let comp1 = l1 <=> l2;
                if(comp1 != Comparison.EqualTo) {
                    comp1
                } else {
                    list1 <=> list2
                }
        }
    }

    instance LowerBound[Path[a]] {
        // The longest list
        pub def minValue(): Path[a] = Bot
    }

    instance PartialOrder[Path[a]] {
        pub def lessEqual(x: Path[a], y: Path[a]): Bool = match (x, y) {
            case (Bot, _)                   => true
            case (Path(_, l1), Path(_, l2)) => l1 >= l2
            case _                          => false
        }
    }

    instance JoinLattice[Path[a]] {
        pub def leastUpperBound(x: Path[a], y: Path[a]): Path[a] = match (x, y) {
            case (Bot, p)                   => p
            case (p, Bot)                   => p
            case (Path(_, l1), Path(_, l2)) => if (l1 <= l2) x else y
        }
    }

    instance MeetLattice[Path[a]] {
        pub def greatestLowerBound(x: Path[a], y: Path[a]): Path[a] = match (x, y) {
            case (Bot, _)                   => Bot
            case (_, Bot)                   => Bot
            case (Path(_, l1), Path(_, l2)) => if (l1 > l2) x else y
        }
    }

    instance Foldable[Path] {
        pub def foldLeft(f: b -> (a -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
            case Bot     => s
            case Path(p, _) => Foldable.foldLeft(f, s, p)
        }

        pub def foldRight(f: a -> (b -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
            case Bot     => s
            case Path(p, _) => Foldable.foldRight(f, s, p)
        }

        pub def foldRightWithCont(f: a -> ((Unit -> b \ ef) -> b \ ef), s: b, t: Path[a]): b \ ef = match t {
            case Bot     => s
            case Path(p, _) => Foldable.foldRightWithCont(f, s, p)
        }
    }

    ///
    /// Returns a `Path` from `x` to `y` of length `l`.
    ///
    pub def init(y: a,  l: Int32, x: a): Path[a] =
        Path(y :: x :: Nil, l)

    ///
    /// Extends the `Path` `p` with `z` of length `l`.
    ///
    pub def cons(z: a, l: Int32, p: Path[a]): Path[a] = match (p) {
        case Bot          => Bot
        case Path(xs, l1) => Path(z :: xs, l1 + l)
    }


    // pub def getFacts(): #{ Road(Int64, Int64) | t } \ {IO, Sys} = 
    //     let path = "${factFolder()}/road-1000000.csv";
    //     let tuples = loadTuplesFromFile(path, ",");
    //     let map = Int64.fromString >> unwrap;
    //     let roads = tuples |> List.map(x -> match x {
    //         case src :: dst :: Nil => (map(src), map(dst))
    //         case _ => exit("Error parsing facts file")
    //     });
    //     inject roads into Road

    pub def getFacts(): #{ Road(Int64, Int64) | t } \ IO + Sys = 
        let path = "${factFolder()}/road-1000000.csv";
        let tuples = loadTuplesFromFile(path, ",");
        let map = Int64.fromString >> unwrap;
        let roads = tuples |> List.map(x -> match x {
            case src :: dst :: Nil => (map(src), map(dst))
            case _ => exit("Error parsing facts file")
        });
        inject roads into Road/2

    pub def getSmallFacts(): #{ Road(Int64, Int64) | t } \ {IO, Sys} =
        let path = "${factFolder()}/road-3000.csv";
        let tuples = loadTuplesFromFile(path, ",");
        let map = Int64.fromString >> unwrap;
        let roads = tuples |> List.map(x -> match x {
            case src :: dst :: Nil => (map(src), map(dst))
            case _ => exit("Error parsing facts file")
        });
        inject roads into Road/2

    pub def runSingle(): Unit \ IO + Sys = Clock.runWithIO(() -> {
        let f = getFacts();
        let r = #{
            Road(x, y) :- Road(y, x).
            Path(x, y) :- Road(x, y).
            Path(x, z) :- Road(y, z), Path(x, y).
            // LongRoadPath(x, z) :- Road(x, y), Road(y, z), if(x != z).
            // LongRoadPath(x, v) :- Road(x, y), Road(y, z), Road(z, v), if(x != z), if(y != v), if(x != v).
            // LongRoadPath(x, w) :- Road(x, y), Road(y, z), Road(z, v), Road(v, w), if(y != v).
            // LongRoadPath(x, w) :- Road(x, y), Road(y, z), Road(z, v), Road(v, w), if(x != z), if(y != v), if(x != v), if(x != y), if (w != y), if (w != z), if (w != x).
            // LongRoadPath(x, w) :- Road(x, y), Road(y, z), Road(z, v), Road(v, w), Road(w, u), if(x != z), if(y != v), if(x != v), if(x != y), if (w != y), if (w != z), if (w != x), if (u != v), if (u != z), if (u != y), if (u != x).
        };
        let startTime = Clock.now();
        let x = query f, r select (x, y) from Path(x, y);
        Common.forceEval(x);
        let endTime = Clock.now();
        println(endTime - startTime)
    })

    pub def runSingleLattice(): Unit \ IO + Sys = Clock.runWithIO(() -> {
        ???;
        // let f = getFacts();
        // Clock.runWithIO(() -> runLatticeWithFacts(f));
        ()
    })

    pub def runWithFacts(f: #{ Road(Int64, Int64) }): Int64 \ IO + Clock = 
        let r = #{
            Road(x, y) :- Road(y, x).
            Path(x, y) :- Road(x, y).
            Path(x, z) :- Path(x, y), Road(y, z).
        };
        let startTime = Clock.now();
        println("Start: ${startTime}");
        let x = (unchecked_cast(query f, r select (x, y) from Path(x, y) as _ \ Clock));
        Common.forceEval(x);
        let endTime = Clock.now();
        endTime - startTime

    pub def runWithFactsShuffled(f: #{ Road(Int64, Int64) }): Int64 \ IO + Clock = 
        let r = #{
            Road(x, y) :- Road(y, x).
            Path(x, y) :- Road(x, y).
            Path(x, z) :- Road(y, z), Path(x, y).
        };
        let x = query f, r select (x, y) from Path(x, y);
        let startTime = Clock.now();
        println("Start: ${startTime}");
        Common.forceEval(x);
        let endTime = Clock.now();
        endTime - startTime

    pub def runLatticeWithFacts(f: #{ Road(Int64, Int64) }): Int64 \ IO + Clock = 
        let r = #{
            Road(x, y) :- Road(y, x).
            Path(x, y; init(y, 1, x)) :- Road(x, y).
            Path(x, z; cons(z, 1, l)) :- Path(x, y; l), Road(y, z).
        };
        let x = query f, r select shortest from Path(x, y; shortest);
        let startTime = Clock.now();
        Common.forceEval(x);
        let endTime = Clock.now();
        endTime - startTime
}