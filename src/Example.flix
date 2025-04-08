def main(): Unit \ IO =
    println("Print");
    let path = #{
        Edge(1,2).
        Path(x, y) :- Edge(x, y), Edge(y, x).
        Path(x, y) :- Path(x, z), Path(y, z).
    };
    println("Print2");
    let r = query path select (x, y) from Path(x,y);
    println(r);
    println("Print6");
    ()


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
