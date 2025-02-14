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


//     struct PredSymMaps[r] {
//         mut counter: Int64
//     }

//     mod PredSymMaps {
        
//         def empty(rc: Region[r]): PredSymMaps[r] \ r =
//             new PredSymMaps @ rc { counter = 0i64 }    
//     }


def main(): Unit \ IO =
println("x");
    let p = #{
    PartDepends("Car",       "Chassis").
    PartDepends("Car",       "Engine").
    PartDepends("Engine",    "Piston").
    PartDepends("Engine",    "Ignition").

    AssemblyTime("Car",     7).
    AssemblyTime("Engine",  2).

    DeliveryDate("Chassis";  2).
    DeliveryDate("Piston";   1).
    DeliveryDate("Ignition"; 7).
};
    let r = query p select (c, d) from DeliveryDate(c; d);
    println(r);

// Computes the delivery date for each component.
// let r = query p select (c, d) from ReadyDate(c; d)
//     println(isConnected());
    // let x = new ReentrantLock();
    // x.lock();

    ()
