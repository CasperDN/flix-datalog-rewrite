import java.util.concurrent.locks.ReentrantLock
import java.lang.Float
import java.lang.reflect.Array

// def isConnected(s: Set[(Int32, Int32)], src: Int32, dst: Int32): Bool =
//     let rules = #{
//         Path(x, y) :- Edge(x, y).
//         Path(x, z) :- Path(x, y), Edge(y, z).
//     };
//     let edges = inject s into Edge;
//     let paths = query edges, rules select true from Path(src, dst);
//     not (paths |> Vector.isEmpty)

// def test(x: List[v]): Unit \ IO =
//     println(v);

def test1(x: Int32): Int32 = x

// def testtt(v: t): #{BBB(t)} with Order[t] =
//     #{BBB(v)}



def cyclic(): #{BBB(Int32)} = 
    #(BBB) -> #{
        BBB(123).
        TTT(123).
    }


def makeArr(): Unit = region rc {
    unchecked_cast (
    let _ = MutList.empty(rc);
    let _ = Array.newInstance(Int32.valueOf(1).getClass(), 10);
    () as _ \ {})}


def main(): Unit \ IO =
    println(query cyclic() select (b) from BBB(b));
    println("x");
    // let y = 1 :: Nil;
    let p = #{
        Test(1).
        AAA(3i64, "hej"; test1(1)).

        // Test(f(x)):- Test(x), Test(x).


        // Path(y, x) :- Edge(y, x).
    };
    let r = query p select (c, e, d) from AAA(c, e; d);
    println(r);

    ()