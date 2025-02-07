import java.util.concurrent.locks.ReentrantLock
def isConnected(s: Set[(Int32, Int32)], src: Int32, dst: Int32): Bool =
    let rules = #{
        Path(x, y) :- Edge(x, y).
        Path(x, z) :- Path(x, y), Edge(y, z).
    };
    let edges = inject s into Edge;
    let paths = query edges, rules select true from Path(src, dst);
    not (paths |> Vector.isEmpty)

def main(): Unit \ IO =
    let x = new ReentrantLock();
    x.lock();

    ()
