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

    // def boxToNormal(box: Boxed): Int64 = match box {
    //     case BoxedBool(x)       => if (x) 1i64 else 0i64
    //     case BoxedChar(x)       => Int32.toInt64(Char.toBmpCodePoint(x)) // TODO: Confirm with Magnus
    //     case BoxedInt8(x)       => Int8.toInt64(x)
    //     case BoxedInt16(x)      => Int16.toInt64(x)
    //     case BoxedInt32(x)      => Int32.toInt64(x)
    //     case BoxedInt64(x)      => x
    //     case BoxedFloat32(x)    => unchecked_cast(Int32.toInt64(Int32.intValue(Float.floatToRawIntBits(Float32.valueOf(x)))) as _ \ {})
    //     case BoxedFloat64(x)    => ???
    //     // case BoxedFloat64(x)    => Double.doubleToRawLongBits(Float64.valueOf(x))
    //     case BoxedObject(x, f)  => ???
    // }

// def testtt(v: t): #{BBB(t)} with Order[t] =
//     #{BBB(v)}



def cyclic(): #{BBB(Int32)} = 
    #(BBB) -> #{
        BBB(123).
        TTT(123).
    }


def makeArr(): Unit = region rc {
    unchecked_cast (
    // let x = Integer[];
    let _ = MutList.empty(rc);
    // let _ = Float;
    // let arr = Array.empty(rc);
    let _ = Array.newInstance(Int32.valueOf(1).getClass(), 10);
    () as _ \ {})}


def main(): Unit \ IO =
    println(query cyclic() select (b) from BBB(b));
    // println(query testtt(1) select (b) from BBB(b));
    // println(query testtt(1i64) select (b) from BBB(b));
    // // println(Int32.toInt64(Float.floatToRawIntBits(Float32.valueOf(1.1f32).floatValue())));
    // println("Arr")
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

    // let p = #{
    //     Test(1).
    //     Test(2).
    //     Res(x):- Test(x).
    //     // Res(x, y):- Test(x), Test(y).
    // };
    // let r = query p select (x) from Res(x);
    // println(r);


// Computes the delivery date for each component.
// let r = query p select (c, d) from ReadyDate(c; d)
//     println(isConnected());
    // let x = new ReentrantLock();
    // x.lock();

    ()
