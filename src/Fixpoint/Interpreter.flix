/*
 * Copyright 2021 Benjamin Dahse
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

mod Fixpoint.Interpreter {
    use Fixpoint.Boxing
    use Fixpoint.Boxing.{Boxing, rebox, debox}
    use PredTrack.PredSymMapInternal
    use Fixpoint.Boxed
    use Fixpoint.Ast.ExecutableRam.{RamStmt, RelOp, RamTerm, BoolExp, RamProgram}
    use Fixpoint.Ast.Ram.{RelSym, toDenotation}
    use Fixpoint.Ast.Shared.Denotation
    use Fixpoint.Helpers.{unwrap}

    type alias Tuple[r: Region] = Array[Int64, r]

    type alias SearchTuple[r: Region] = Tuple[r]

    pub type alias Index[r: Region] = BPlusTree[r]

    pub type alias Indexes[r: Region] = Array[Index[r], r]

    pub type alias Database[r: Region] = MutMap[RelSym, MutMap[Vector[Int64], Int64, r], r]

    pub type alias DatabaseExternal[r: Region] = MutMap[RelSym, MutMap[Vector[Boxed], Boxed, r], r]

    pub type alias SearchEnv[r: Region] = (
        Vector[SearchTuple[r]], 
        Vector[SearchTuple[r]], 
        Array[Array[Int64, r], r],
        Array[Boxed, r]
    )

    pub type alias Context[r: Region] = (
        Indexes[r], 
        SearchEnv[r], 
        Boxing[r]
    )

    // @Internal
    // pub def interpret(rc: Region[r], input: (RamProgram, Boxing[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
    //     ???


    // @Internal
    // pub def interpretWithDatabase(rc: Region[r], db: DatabaseExternal[r], input: (RamProgram, Boxing[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
    //     ???

    // pub def lubWith(
    //     index: Int32, 
    //     boxing: Boxing[r], 
    //     lub: Boxed -> Boxed -> Boxed, 
    //     l1: Int64, 
    //     l2: Int64
    // ): Int64 =
    // ???
        // let box1 = rebox(l1, index, boxing);
        // let box2 = rebox(l2, index, boxing);
        // debox(box1 `lub` box2, index, boxing)
    
    pub def mkIndex(
        rc: Region[r], 
        relSym: RelSym, 
        search: Vector[Int32], 
        tuples: Vector[(Vector[Int64], Boxed)]
    ): Index[r] \ r = 
        let index = BPlusTree.empty(rc, search);
        if(Vector.isEmpty(tuples)) 
            index
        else {
            Vector.forEach(match (nonLat, lat) -> {
                let asArray = unchecked_cast(nonLat as Array[Int64, r]);
                match toDenotation(relSym) {
                    case Denotation.Relational => 
                        BPlusTree.insert(asArray, lat, index)
                    case Denotation.Latticenal(_, _, lub, _) =>
                        BPlusTree.putWith(lub, asArray, lat, index)
                }
            }, tuples);
            index
        }

    @Internal
    pub def interpret(rc: Region[r], input: (RamProgram, Boxing[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
        let (program, boxing) = input;
        let indexes = match program {
            case RamProgram.Program(_, facts, _, (indexMap, posMap), _) => 
                let indexes = Array.empty(rc, snd(unwrap(Map.maximumValue(posMap))));
                facts |>
                Map.forEach(relSym -> tuples -> {
                    match Map.get(relSym, indexMap) {
                        case Some(v) => v
                        case None => bug!("In Interpreter.interpret: ${relSym} has no index!")
                    } |>
                    Vector.forEachWithIndex(i -> search -> {
                        let pos = match Map.get((relSym, i), posMap) {
                            case Some(v) => v
                            case None => bug!("In Interpreter.interpret: search ${(relSym, i)} has no position!")
                        };
                        Array.put(mkIndex(rc, relSym, search, tuples), pos, indexes)
                    })
                });
                indexes
        };
        interpretWithDatabaseInternal(rc, indexes, boxing, program)

    @Internal
    pub def interpretWithDatabase(rc: Region[r], input: (RamProgram, Database[r], Boxing[r])): (DatabaseExternal[r], PredSymMapInternal) \ r = 
        ???
        // let (program, db, boxing) = input;
        // interpretWithDatabaseInternal(rc, db, boxing, program)

    @Internal
    pub def interpretWithDatabaseInternal(
        rc: Region[r], 
        db: Indexes[r], 
        boxing: Boxing[r], 
        program: RamProgram
    ): (DatabaseExternal[r], PredSymMapInternal) \ r = match Fixpoint.Debugging.notifyPreInterpret(program) {
        case RamProgram.Program(stmt, _, predState, _, arities) =>
            let minEnv = arities |> Vector.map(x -> Array.repeat(rc, x, Int64.minValue()));
            let maxEnv = arities |> Vector.map(x -> Array.repeat(rc, x, Int64.maxValue()));
            let tupleEnv = arities |> Vector.length |> Array.empty(rc);
            let latEnv = arities |> Vector.length |> Array.empty(rc);
            let env = (minEnv, maxEnv, tupleEnv, latEnv);
            let ctxt = (db, env, boxing);
            evalStmt(rc, ctxt, stmt);
            (marshallDb(rc, db, boxing), predState)
    }


    def marshallDb(rc: Region[r], db: Indexes[r], boxing: Boxing[r]): DatabaseExternal[r] = ???

    def evalStmt(rc: Region[r], ctxt: Context[r], stmt: RamStmt): Unit \ r = 
        match stmt {
        case RamStmt.Insert(relOp) =>
            evalOp(rc, ctxt, relOp)
        case RamStmt.Merge(srcIndex, dstIndex, lub, index) =>
            let (db, env, boxing) = ctxt;
            // let dst = Array.get(dstSym, db);
            let src = Array.get(srcIndex, db);
            let dst = Array.get(dstIndex, db);
            if (index == -1) {
                BPlusTree.merge(src, dst)
            } else
                BPlusTree.mergeWith(lub, src, dst)
        case RamStmt.Swap(lhs, rhs) =>
            let (db, _, _) = ctxt;
            let temp = Array.get(lhs, db);
            Array.put(Array.get(rhs, db), lhs, db);
            Array.put(temp, rhs, db)
        case RamStmt.Purge(index) => 
            let (db, _, _) = ctxt;
            let oldIndex = Array.get(index, db);
            let newIndex = BPlusTree.empty(rc, BPlusTree.getSearch(oldIndex));
            Array.put(newIndex, index, db)
        case RamStmt.Seq(stmts) => Vector.forEach(evalStmt(rc, ctxt), stmts)
        case RamStmt.Until(test, body) =>
            if (evalBoolExp(rc, ctxt, test)) {
                ()
            } else {
                evalStmt(rc, ctxt, body);
                evalStmt(rc, ctxt, stmt)
            }
        case RamStmt.Comment(_) => ()
        case RamStmt.Par(_) => ???
    }

    // // def allocEnv(rc: Region[r], depth: Int32, relOp: RelOp): SearchEnv[r] \ r = match relOp {
    // //     case RelOp.Search(_, _, _, body) => allocEnv(rc, depth + 1, body)
    // //     case RelOp.Query(_, _, _, _, body) => allocEnv(rc, depth + 1, body)
    // //     case RelOp.Functional(_, _, _, body, _, _) => allocEnv(rc, depth + 1, body)
    // //     case RelOp.Project(_, _, _) => (Array.repeat(rc, depth, Vector.empty()), Array.empty(rc, depth))
    // //     case RelOp.If(_, then) => allocEnv(rc, depth, then)
    // // }

    def evalOp(rc: Region[r], ctxt: Context[r], op: RelOp): Unit \ r = 
        let (db, env, boxing) = ctxt; 
        match op {
            case RelOp.Search(tuplePos, searchIndex, writes, body) =>
                let (_, _, tupleEnv, _) = env;
                Array.get(searchIndex, db) |> 
                BPlusTree.forEach(t -> _ -> {
                    Array.put(t, tuplePos, tupleEnv);
                    evalOp(rc, ctxt, body)
                })
            case RelOp.Query(tuplePos, searchIndex, writes, body) =>
                let (minEnv, maxEnv, tupleEnv, _) = env;
                Array.get(searchIndex, db) |>
                BPlusTree.rangeQueryWith(
                    t -> _ -> {
                        Array.put(t, tuplePos, tupleEnv);
                        writes |> Vector.forEach(match (srcIndex, dst, dstIndex) -> {
                            Array.put(Array.get(srcIndex, t), dstIndex, Vector.get(dst, minEnv));
                            Array.put(Array.get(srcIndex, t), dstIndex, Vector.get(dst, maxEnv))
                        });
                        evalOp(rc, ctxt, body)
                    },
                    Vector.get(tuplePos, minEnv),
                    Vector.get(tuplePos, maxEnv)
                )
            case RelOp.SearchLattice(tuplePos, searchIndex, meetWith, glb, writes, body) => 
                let (_, _, tupleEnv, latEnv) = env;
                Array.get(searchIndex, db) |> 
                BPlusTree.forEach(t -> l -> {
                    Array.put(t, tuplePos, tupleEnv);
                    if (meetWith == tuplePos) Array.put(l, tuplePos, latEnv) 
                    else Array.put(l `glb` Array.get(meetWith, latEnv), tuplePos, latEnv);
                    evalOp(rc, ctxt, body)
                })
            case RelOp.QueryLattice(tuplePos, searchIndex, meetWith, glb, writes, body) => 
                let (minEnv, maxEnv, tupleEnv, latEnv) = env;
                Array.get(searchIndex, db) |>
                BPlusTree.rangeQueryWith(
                    t -> l -> {
                        Array.put(t, tuplePos, tupleEnv);
                        if (meetWith == tuplePos) Array.put(l, tuplePos, latEnv) 
                        else Array.put(l `glb` Array.get(meetWith, latEnv), tuplePos, latEnv);
                        writes |> Vector.forEach(match (srcIndex, dst, dstIndex) -> {
                            Array.put(Array.get(srcIndex, t), dstIndex, Vector.get(dst, minEnv));
                            Array.put(Array.get(srcIndex, t), dstIndex, Vector.get(dst, maxEnv))
                        });
                        evalOp(rc, ctxt, body)
                    },
                    Vector.get(tuplePos, minEnv),
                    Vector.get(tuplePos, maxEnv)
                )
            case RelOp.Functional(i, f, terms, _, body, i1, _) =>
                let args = terms |> 
                    Vector.mapWithIndex(_ -> x -> evalBoxedTerm(env, boxing, x));

                let result = f(args)|> 
                    Vector.map(vec -> Vector.mapWithIndex(i_ -> x -> debox(x, Vector.get(i_, i1), boxing), vec));

                ???
                // let (tupleEnv, _latEnv) = env;
                // foreach (t <- result) {
                //     Array.put(t, i, tupleEnv);
                //     evalOp(rc, ctxt, body)
                // }
            case RelOp.Project(terms, rel, bot, leq, lub, index) =>
                let relIndex = Array.get(rel, db);
                if (index == -1)
                    let tuple = unchecked_cast(Vector.map(evalTerm(env, boxing), terms) as Array[Int64, r]);
                    BPlusTree.insert(tuple, Boxed.None, relIndex)
                else
                    let len = Vector.length(terms);
                    let tuple = Array.empty(rc, len - 1);
                    terms |> Vector.forEachWithIndex(i -> term -> {
                        if (i < len) 
                            Array.put(evalTerm(env, boxing, term), i, tuple)
                        else ()
                    });
                    let latVal = evalBoxedTerm(env, boxing, Vector.get(len - 1, terms));
                    if (latVal `leq` bot) ()
                    else BPlusTree.putWith(lub, tuple, latVal, relIndex)
            case RelOp.If(test, then) =>
                if (evalBoolExp(rc, ctxt, test)) {
                    evalOp(rc, ctxt, then)
                } else {
                    ()
                }
        }

    // def evalQuery(env: SearchEnv[r], boxing: Boxing[r], qry: List[(Int32, RamTerm)], tuple: Vector[Int64]): Comparison \ r + r =
    //     match qry {
    //         case Nil => Comparison.EqualTo
    //         case (j, t) :: tl => match Vector.get(j, tuple) <=> evalTerm(env, boxing, t) {
    //             case Comparison.EqualTo => evalQuery(env, boxing, tl, tuple)
    //             case cmp => cmp
    //         }
    //     }

    def evalBoolExp(rc: Region[r], ctxt: Context[r], exps: Vector[BoolExp]): Bool \ r =
        let (db, env, boxing) = ctxt;
        let evalT = evalTerm(env, boxing);
        exps |> Vector.forAll(exp -> match exp {
            case BoolExp.IsEmpty(rel) => BPlusTree.isEmptyThreadUnsafe(Array.get(rel, db))
            case BoolExp.NotMemberOf(terms, rel, leq, index) =>
                let relIndex = Array.get(rel, db);
                if (index == -1)
                    let tuple = Vector.map(evalT, terms);
                    not BPlusTree.memberOfThreadUnsafe(unchecked_cast(tuple as Array[Int64, r]), relIndex)
                else {
                    let len = Vector.length(terms);
                    let tuple = Array.empty(rc, len - 1);
                    terms |> Vector.forEachWithIndex(i -> term -> {
                        if (i < len) 
                            Array.put(evalT(term), i, tuple)
                        else ()
                    });
                    let latVal = evalBoxedTerm(env, boxing, Vector.get(len - 1, terms));
                    let curLatVal = BPlusTree.getWithDefault(tuple, Boxed.None, relIndex);
                    not (latVal `leq` curLatVal)
                }
            case BoolExp.Eq(lhs, rhs) => evalTerm(env, boxing, lhs) == evalTerm(env, boxing, rhs)
            case BoolExp.Guard0(f) => f()
            case BoolExp.Guard1(f, t, i) =>
                let v = evalT(t);
                let boxed = rebox(v, i, boxing);
                f(boxed)
            case BoolExp.Guard2(f, t1, t2, i1, i2) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let boxed1 = rebox(v1, i1, boxing);
                let boxed2 = rebox(v2, i2, boxing);
                f(boxed1)(boxed2)
            case BoolExp.Guard3(f, t1, t2, t3, i1, i2, i3) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let boxed1 = rebox(v1, i1, boxing);
                let boxed2 = rebox(v2, i2, boxing);
                let boxed3 = rebox(v3, i3, boxing);
                f(boxed1)(boxed2)(boxed3)
            case BoolExp.Guard4(f, t1, t2, t3, t4, i1, i2, i3, i4) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let boxed1 = rebox(v1, i1, boxing);
                let boxed2 = rebox(v2, i2, boxing);
                let boxed3 = rebox(v3, i3, boxing);
                let boxed4 = rebox(v4, i4, boxing);
                f(boxed1)(boxed2)(boxed3)(boxed4)
            case BoolExp.Guard5(f, t1, t2, t3, t4, t5, i1, i2, i3, i4, i5) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let v5 = evalT(t5);
                let boxed1 = rebox(v1, i1, boxing);
                let boxed2 = rebox(v2, i2, boxing);
                let boxed3 = rebox(v3, i3, boxing);
                let boxed4 = rebox(v4, i4, boxing);
                let boxed5 = rebox(v5, i5, boxing);
                f(boxed1)(boxed2)(boxed3)(boxed4)(boxed5)
        })

    def evalBoxedTerm(env: SearchEnv[r], boxing: Boxing[r], term: RamTerm): Boxed \ {r} = 
        let evalT = evalBoxedTerm(env, boxing);
        match term {
            case RamTerm.Lit(_, b) => b
            case RamTerm.LoadFromTuple(tupleIndex, indexInTuple, i) => 
                let (_, _, tupleEnv, _) = env;
                let unboxed = Array.get(tupleIndex, Array.get(indexInTuple, tupleEnv));
                rebox(unboxed, i, boxing)
            case RamTerm.LoadLatVar(index) =>
                let (_, _, _, latEnv) = env;
                Array.get(index, latEnv)
            case RamTerm.Meet(cap, lhs, rhs, _) =>
                let boxed1 = evalBoxedTerm(env, boxing, lhs);
                let boxed2 = evalBoxedTerm(env, boxing, rhs);
                boxed1 `cap` boxed2
            case RamTerm.App0(f, _) => f()
            case RamTerm.App1(f, t, _, _) =>
                let v1 = evalT(t); // Could make an eval that returns Boxed. Would be slightly more performant.
                f(v1)
            case RamTerm.App2(f, t1, t2, _, _, _) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                f(v1)(v2)
            case RamTerm.App3(f, t1, t2, t3, _, _, _, _) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                f(v1)(v2)(v3)
            case RamTerm.App4(f, t1, t2, t3, t4, _, _, _, _, _) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                f(v1)(v2)(v3)(v4)
            case RamTerm.App5(f, t1, t2, t3, t4, t5, _, _, _, _, _, _) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let v5 = evalT(t5);
                f(v1)(v2)(v3)(v4)(v5)
        }

    def evalTerm(env: SearchEnv[r], boxing: Boxing[r], term: RamTerm): Int64 \ {r} = 
        let evalT = evalTerm(env, boxing);
        match term {
            case RamTerm.Lit(v, _) => v
            case RamTerm.LoadFromTuple(tupleIndex, indexInTuple, _) =>
                let (_, _, tupleEnv, _) = env;
                Array.get(tupleIndex, Array.get(indexInTuple, tupleEnv))
            case RamTerm.LoadLatVar(_) => ???
            case RamTerm.Meet(cap, lhs, rhs, i) =>
                let boxed1 = rebox(evalTerm(env, boxing, lhs), i, boxing);
                let boxed2 = rebox(evalTerm(env, boxing, rhs), i, boxing);
                debox(boxed1 `cap` boxed2, i, boxing)
            case RamTerm.App0(f, i) =>
                debox(f(), i, boxing)
            case RamTerm.App1(f, t, i1, i) =>
                let v = evalT(t); // Could make an eval that returns Boxed. Would be slightly more performant.
                let boxed1 = rebox(v, i1, boxing);
                debox(f(boxed1), i, boxing)
            case RamTerm.App2(f, t1, t2, i1, i2, i) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let boxed1 = rebox(v1, i1, boxing);
                let boxed2 = rebox(v2, i2, boxing);
                debox(f(boxed1)(boxed2), i, boxing)
            case RamTerm.App3(f, t1, t2, t3, i1, i2, i3, i) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let boxed1 = rebox(v1, i1, boxing);
                let boxed2 = rebox(v2, i2, boxing);
                let boxed3 = rebox(v3, i3, boxing);
                debox(f(boxed1)(boxed2)(boxed3), i, boxing)
            case RamTerm.App4(f, t1, t2, t3, t4, i1, i2, i3, i4, i) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let boxed1 = rebox(v1, i1, boxing);
                let boxed2 = rebox(v2, i2, boxing);
                let boxed3 = rebox(v3, i3, boxing);
                let boxed4 = rebox(v4, i4, boxing);
                debox(f(boxed1)(boxed2)(boxed3)(boxed4), i, boxing)
            case RamTerm.App5(f, t1, t2, t3, t4, t5, i1, i2, i3, i4, i5, i) =>
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let v5 = evalT(t5);
                let boxed1 = rebox(v1, i1, boxing);
                let boxed2 = rebox(v2, i2, boxing);
                let boxed3 = rebox(v3, i3, boxing);
                let boxed4 = rebox(v4, i4, boxing);
                let boxed5 = rebox(v5, i5, boxing);
                debox(f(boxed1)(boxed2)(boxed3)(boxed4)(boxed5), i, boxing)
        }
}
