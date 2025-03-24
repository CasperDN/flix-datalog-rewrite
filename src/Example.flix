def main(): Unit \ IO =
    let path = #{
        Edge(1,2).

        Path(x, y) :- Edge(x, y).
        Path(x, y) :- Path(x, z), Path(z, y).
    };
    let hej = #{
        Hej1(1, 2, 3).
        Hej2(2, 3, 4).
        Hej3(x, w) :- Hej1(x, y, z), Hej2(y, z, w).
        Hej3(y, w) :- Hej1(y, z, w), Hej2(_, y, z).
    };
    let _ = query path select (x, y) from Path(x,y);
    let r = query hej select (x, w) from Hej3(x, w);
    println(r)
