import java.util.concurrent.locks.ReentrantLock
import java.lang.Float
import java.lang.System;

// def repeatN(f: Unit -> Bool \ ef, callNum: Int64): Bool \ ef = 
//     def repeatNInternal(callNumInternal: Int64, res: Bool): Bool \ ef = {
//         if (callNumInternal <= 0i64) res else {
//             let f_ = f(); repeatNInternal(callNumInternal - 1i64, res and f_)
//         }
//     };
//     repeatNInternal(callNum, true)


def main(): Unit  =
    // let n = 10_000_000;
    // let _ = Random.runWithIO(() -> repeatN(() -> {Random.randomInt64(); true}, 10i64));
    // let vec = (Random.handleWithSeed(0i64, () -> Vector.map(_ -> Random.randomInt32(), Vector.range(0, n))))();
    // println(Vector.last(vec));

    ()
