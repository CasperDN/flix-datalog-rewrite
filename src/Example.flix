import java.util.concurrent.locks.ReentrantLock
def isConnected(s: Set[(Int32, Int32)], src: Int32, dst: Int32): Bool =
    let rules = #{
        Path(x, y) :- Edge(x, y).
        Path(x, z) :- Path(x, y), Edge(y, z).
    };
    let edges = inject s into Edge;
    let paths = query edges, rules select true from Path(src, dst);
    not (paths |> Vector.isEmpty)


// struct Person[r] {
//     mut height: Int32
// }


// mod Person {
//     pub def mkLuckyLuke(rc: Region[r]): Person[r] \ r =
//         new Person @ rc { height = 185 }
// }


//     struct PredTrack[r] {
//         mut counter: Int64
//     }

//     mod PredTrack {
        
//         def empty(rc: Region[r]): PredTrack[r] \ r =
//             new PredTrack @ rc { counter = 0i64 }    
//     }

// def test(x: List[v]): Unit \ IO =
//     println(v);

def test1(x: Int32): Int32 = x

def main(): Unit \ IO =
// println("x");
    // let y = 1 :: Nil;
    // let p = #{
    //     Test(1).
    //     Edge(3, "hej"; test1(1)).

    //     Test(x):- Test(x), Test(x).


    //     // Path(y, x) :- Edge(y, x).
    // };
    // let r = query p select (c, e, d) from Edge(c, e; d);
    // println(r);

    let p = #{
        Test(1).
        Test(2).
        Res(x):- Test(x).
        // Res(x, y):- Test(x), Test(y).
    };
    let r = query p select (x) from Res(x);
    println(r);


// Computes the delivery date for each component.
// let r = query p select (c, d) from ReadyDate(c; d)
//     println(isConnected());
    // let x = new ReentrantLock();
    // x.lock();

    ()
