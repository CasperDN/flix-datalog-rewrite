def main(): Unit \ IO =
    let path = #{
        Edge(1,2).

        Path(x, y) :- Edge(x, y).
        Path(x, y) :- Path(x, z), Path(z, y).
    };
    let indexSelection1 = #{
        A(1, 2, 3).
        B(1, 2, 3).
        B(x, y, z) :- A(x, y, z), B(x, _, _).
        B(x, y, z) :- A(x, y, z), B(x, y, _).
        B(x, y, z) :- A(x, y, z), B(x, y, z).
        B(x, y, z) :- A(x, y, z), B(x, z, _).
    };
    let indexSelection2 = #{
        A(1, 2, 3).
        B(1, 2, 3).
        B(x, y, z) :- A(x, y, z), B(x, _, z).
        B(x, y, z) :- A(x, y, z), B(x, y, _).
        B(x, y, z) :- A(x, y, z), B(x, y, z).
        B(x, y, z) :- A(x, y, z), B(x, z, _).
    };
    let _ = query path select (x, y) from Path(x,y);
    let _ = query indexSelection1 select (x, y, z) from B(x, y, z);
    let r = query indexSelection2 select (x, y, z) from B(x, y, z);
    println(r)
