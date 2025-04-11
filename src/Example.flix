def main(): Unit \ IO =
    println("Print");
    // let map = Map.empty();
    // println();
    Clock.runWithIO(() ->
        let start = Clock.currentTime(TimeUnit.Seconds);
        let map = List.map(x -> (x, x + 1), List.range(1, 20000));
        let injected = inject map into Edge;
        let path = injected <+> #{
            // Edge(x, y) :- Edge(y, x).
            Path(x, y) :- Edge(x, y).
            Path(x, y) :- Path(x, z), Edge(z, y).
        };
        // let path = #{
        //     Edge(1,2).
        //     Edge(2,3).
        //     Edge(3,4).
        //     Edge(x, y) :- Edge(y, x).
        //     Path(x, y) :- Edge(x, y).
        //     Path(x, y) :- Edge(x, z), Path(z, y), if (x < y).
        // };
        println("Print2");
        let r = query path select (x, y) from Path(x,y);
        // println(r);
        let x = Vector.head(r);
        println(x);
        println(Vector.length(r));
        let end = Clock.currentTime(TimeUnit.Seconds);
        println("Took: ${end - start} s");
        println("Print6")
    );
    ()

def isPrime(x: Int32): Bool = 
    ???

def primesInRange(b: Int32, e: Int32): Vector[Int32] = 
    Vector.range(b, e) |> Vector.filter(isPrime)

def main3(): Unit \ IO =
    let r = #{
        R(2).
        // R(3).
        R(p) :- P(b), Q(e), let p = primesInRange(b, e).
    };
    println(query r select p from R(p))

// def main(): Unit \ IO =
//     println("Print");
//     let path = #{
//         Edge(1,2).

//         Path(x, y) :- Edge(x, y).
//         Path(x, y) :- Path(x, z), Path(z, y).
//     };
//     let indexSelection1 = #{
//         A(1, 2, 3).
//         B(1, 2, 3).
//         B(x, y, z) :- A(x, y, z), B(x, _, z).
//         B(x, y, z) :- A(x, y, z), B(x, _, _).
//         B(x, y, z) :- A(x, y, z), B(x, y, _).
//         B(x, y, z) :- A(x, y, z), B(x, y, z).
//     };
//     let indexSelection2 = #{
//         A(1, 2, 3).
//         B(1, 2, 3).
//         B(x, y, z) :- A(x, y, z), B(x, _, z).
//         B(x, y, z) :- A(x, y, z), B(x, y, _).
//         B(x, y, z) :- A(x, y, z), B(x, y, z).
//     };
//     println("Print2");
//     let _ = query path select (x, y) from Path(x,y);
//     println("Print3");
//     let r = query indexSelection1 select (x, y, z) from B(x, y, z);
//     println("Print4");
//     let _ = query indexSelection2 select (x, y, z) from B(x, y, z);
//     println("Print5");
//     println(r);
//     println("Print6");
//     ()
