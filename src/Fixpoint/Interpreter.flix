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

instance Order[Array[a, r]] with Order[a] {
    pub def compare(x: Array[a, r], y: Array[a, r]): Comparison = 
        let len = Array.length(x);
        def loop(i: Int32): Comparison = 
            if(i >= len)
                Comparison.EqualTo
            else {
                let comp = unchecked_cast(Array.get(i, x) <=> Array.get(i, y) as _ \ {});
                match comp {
                    case Comparison.EqualTo => loop(i + 1)
                    case _ => comp
                }
            };
        loop(0)
}

instance Eq[Array[a, r]] with Eq[a] {
    pub def eq(x: Array[a, r], y: Array[a, r]): Bool = 
        let len = Array.length(x);
        def loop(i: Int32): Bool = 
            if(i >= len)
                true
            else {
                if (unchecked_cast(Array.get(i, x) == Array.get(i, y) as _ \ {})) loop(i + 1)
                else false
            };
    loop(0)
}

mod Fixpoint.Interpreter {
    use Fixpoint.Ast.ExecutableRam.RamProgram.Program
    use Fixpoint.Normalization
    use Fixpoint.Normalization.Normalization
    use PredTrack.PredSymMapInternal
    use Fixpoint.Boxed
    use Fixpoint.Ast.ExecutableRam.{RamStmt, RelOp, RamTerm, BoolExp, RamProgram}
    use Fixpoint.Ast.Ram.{RelSym, toDenotation}
    use Fixpoint.Ast.Shared.Denotation

    type alias Tuple[r: Region] = Array[Int64, r]

    type alias SearchTuple[r: Region] = Tuple[r]

    pub type alias Index[r: Region] = MutMap[Tuple[r], Int64, r]

    pub type alias Indexes[r: Region] = Array[Index[r], r]

    pub type alias Database[r: Region] = MutMap[RelSym, MutMap[Vector[Int64], Int64, r], r]

    pub type alias DatabaseExternal[r: Region] = MutMap[RelSym, MutMap[Vector[Boxed], Boxed, r], r]

    pub type alias SearchEnv[r: Region] = (Array[SearchTuple[r], r], Array[SearchTuple[r], r])

    pub type alias Denotations[r: Region] = Array[Denotation, r]

    pub type alias Context[r: Region] = (
        Indexes[r], 
        SearchEnv[r], 
        Denotations[r],
        Normalization[r]
    )

    // @Internal
    // pub def interpret(rc: Region[r], input: (RamProgram, Normalization[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
    //     ???


    // @Internal
    // pub def interpretWithDatabase(rc: Region[r], db: DatabaseExternal[r], input: (RamProgram, Normalization[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
    //     ???


    def _unwrap(x: Option[a]): a = match x {
        case Some(v) => v
        case None => ???
    }

    pub def lubWith(
        index: Int32, 
        norm: Normalization[r], 
        lub: Boxed -> Boxed -> Boxed, 
        l1: Int64, 
        l2: Int64
    ): Int64 =
        let box1 = Normalization.unNormalizeReal(l1, index, norm);
        let box2 = Normalization.unNormalizeReal(l2, index, norm);
        Normalization.normalizeBox(box1 `lub` box2, index, norm)
    
    pub def mkIndex(
        rc: Region[r], 
        relSym: RelSym, 
        search: Vector[Int32], 
        tuples: Vector[Vector[Int64]],
        norm: Normalization[r]    
    ): Index[r] \ r = 
        let index = BPlusTree.empty(rc, 64, search);
        if(Vector.isEmpty(tuples)) 
            index
        else
            Vector.forEach(tuple -> {
                match toDenotation(relSym) {
                    case Denotation.Relational => 
                    BPlusTree.insert(tuple, 0, index)
                    // (tuple, 0i64, _ -> _ -> 0i64)
                    case Denotation.Latticenal(_, _, lub, _) =>
                        let (vec1, vec2) = Vector.splitAt(Vector.length(tuple) - 1, tuple);
                        let (nonLat, lat) = (vec1, Vector.get(0, vec2));
                        BPlusTree.putWith(lubWith(index, norm, lub), nonLat, lat, index)
                }
            }, tuples);
            index
        

    @Internal
    pub def interpret(rc: Region[r], input: (RamProgram, Normalization[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
        let (program, norm) = input;
        let indexes = match program {
            case Program(_, facts, _, (indexMap, posMap), arities, denotations) => 
                let indexes = Array.empty(rc, Map.maximumValue(posMap));
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
        interpretWithDatabaseInternal(rc, indexes, norm, program)

    @Internal
    pub def interpretWithDatabase(rc: Region[r], input: (RamProgram, Database[r], Normalization[r])): (DatabaseExternal[r], PredSymMapInternal) \ r = 
    ???
    // let (program, db, norm) = input;
    // interpretWithDatabaseInternal(rc, db, norm, program)

    @Internal
    pub def interpretWithDatabaseInternal(
        rc: Region[r], 
        db: Indexes[r], 
        norm: Normalization[r], 
        program: RamProgram
    ): (DatabaseExternal[r], PredSymMapInternal) \ r = match Fixpoint.Debugging.notifyPreInterpret(program) {
        case RamProgram.Program(stmt, _, predState, _, arities, denotations) =>
            let minEnv = arities |> Vector.map(x -> Array.repeat(rc, x, Int64.minValue()));
            let maxEnv = arities |> Vector.map(x -> Array.repeat(rc, x, Int64.maxValue()));
            let env = (minEnv, maxEnv);
            let den = denotations |> Vector.toArray(rc);
            let ctxt = (db, env, den, norm);
            evalStmt(rc, ctxt, stmt);
            (marshallDb(rc, db, norm), predState)
    }


    def marshallDb(rc: Region[r], db: Indexes[r], norm: Normalization[r]): DatabaseExternal[r] = ???

    def evalStmt(rc: Region[r], ctxt: Context[r], stmt: RamStmt): Unit \ r = match stmt {
        case RamStmt.Insert(relOp) => evalOp(rc, ctxt, relOp)
        case RamStmt.Merge(srcIndex, dstIndex, index) =>
            let (db, env, den, norm) = ctxt;
            // let dst = Array.get(dstSym, db);
            let src = Array.get(srcIndex, db);
            let dst = Array.get(dstIndex, db);
            match Array.get(srcIndex, den) {
                case Denotation.Relational => BPlusTree.merge(src, dst)
                case Denotation.Latticenal(_, _, lub, _) => 
                    BPlusTree.mergeWith(lubWith(index, norm, lub), src, dst)
            }
        case RamStmt.Swap(lhs, rhs) =>
            let (db, _, _, _) = ctxt;
            let temp = Array.get(lhs, db);
            Array.put(lhs, Array.get(rhs, db), db);
            Array.put(rhs, temp, db)
        case RamStmt.Purge(index) => 
            let (db, _, _, _) = ctxt;
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

    // def allocEnv(rc: Region[r], depth: Int32, relOp: RelOp): SearchEnv[r] \ r = match relOp {
    //     case RelOp.Search(_, _, _, body) => allocEnv(rc, depth + 1, body)
    //     case RelOp.SearchWithIndex(_, _, _, _, body) => allocEnv(rc, depth + 1, body)
    //     case RelOp.Functional(_, _, _, body, _, _) => allocEnv(rc, depth + 1, body)
    //     case RelOp.Project(_, _, _) => (Array.repeat(rc, depth, Vector.empty()), Array.empty(rc, depth))
    //     case RelOp.If(_, then) => allocEnv(rc, depth, then)
    // }

    def evalOp(rc: Region[r], ctxt: Context[r], op: RelOp): Unit \  r  = 
        let (db, env, den, norm) = ctxt; 
        match op {
            case RelOp.Search(i, index, _, body) =>
                BPlusTree.forEach(t -> l -> evalOp(rc, ctxt, body), Array.get(index, db))
            case RelOp.SearchWithIndex(i, index, qry, _, body) =>
                let (minEnv, maxEnv) = env;
                let toSend = Vector.map(x -> match x {
                    // case QueryExp.Eq(RamTerm.RowLoad(tupleID, index), t2) => (index, t2)
                    case BoolExp.Eq(RamTerm.LoadIndex(index), t2) => (index, t2)
                    case BoolExp.Eq(t1, RamTerm.LoadIndex(index)) => (index, t1)
                    case _ => unchecked_cast(println("Hello ${Debug.stringify(x)}") as _ \ r); ???
                }, qry);
                BPlusTree.rangeQueryWith(
                    t -> l -> evalOp(rc, ctxt, body), 
                    Array.get(i, minEnv), 
                    Array.get(i, maxEnv), 
                    Array.get(index, db)
                )
            case RelOp.Functional(i, f, terms, body, i1, _) =>
                let args = terms |> 
                    Vector.mapWithIndex(i_ -> x -> Normalization.unNormalizeReal(evalTerm(env, norm, x), Vector.get(i_, i1), norm));

                let result = f(args)|> 
                    Vector.map(vec -> Vector.mapWithIndex(i_ -> x -> Normalization.normalizeBox(x, Vector.get(i_, i1), norm), vec));

                let (tupleEnv, _latEnv) = env; // TODO: Do we ever need to use latEnv?
                foreach (t <- result) {
                    Array.put(t, i, tupleEnv);
                    evalOp(rc, ctxt, body)
                }
            case RelOp.Project(terms, ramSym, index) =>
                let rel = MutMap.getOrElsePut(ramSym, MutMap.empty(rc), db);
                match toDenotation(ramSym) {
                    case Denotation.Relational =>
                        let tuple = Vector.map(evalTerm(env, norm), terms);
                        MutMap.put(tuple, Reflect.default(), rel)
                    case Denotation.Latticenal(bot, leq, lub, _) =>
                        // assume that length(terms) > 0
                        let len = Vector.length(terms);
                        let keyList = terms |> Vector.map(evalTerm(env, norm));
                        let leqWrap = l1 -> l2 -> Normalization.unNormalizeReal(l1, index, norm) `leq` l2;
                        let lubWrap = l1 -> l2 -> Normalization.normalizeBox(Normalization.unNormalizeReal(l1, index, norm) `lub` Normalization.unNormalizeReal(l2, index, norm), index, norm);
                        let (key, latValList) = Vector.splitAt(len - 1, keyList);
                        let latVal = match Vector.head(latValList) {
                            case None => bug!("Found predicate without terms")
                            case Some(k) => k
                        };
                        if (latVal `leqWrap` bot) ()
                        else MutMap.putWith(lubWrap, key, latVal, rel)
                }
            case RelOp.If(test, then) =>
                if (evalBoolExp(rc, db, env, norm, test)) {
                    evalOp(rc, ctxt, then)
                } else {
                    ()
                }
            case _ => ()
        }

    def evalQuery(env: SearchEnv[r], norm: Normalization.Normalization[r], qry: List[(Int32, RamTerm)], tuple: Vector[Int64]): Comparison \ r + r =
        match qry {
            case Nil => Comparison.EqualTo
            case (j, t) :: tl => match Vector.get(j, tuple) <=> evalTerm(env, norm, t) {
                case Comparison.EqualTo => evalQuery(env, norm, tl, tuple)
                case cmp => cmp
            }
        }

    def evalBoolExp(rc1: Region[r], ctxt: Context[r], exps: Vector[BoolExp]): Bool \ r =
        let (db, env, den, norm) = ctxt;
        exps |> Vector.forAll(exp -> match exp {
            case BoolExp.IsEmpty(index) => BPlusTree.isEmptyThreadUnsafe(Array.get(index, db))
            case BoolExp.NotMemberOf(terms, ramSym, index) =>
                let rel = Array.get(index, db);
                match Array.get(index, den) {
                    case Denotation.Relational =>
                        let tuple = Vector.map(evalTerm(env, norm), terms);
                        not BPlusTree.memberOfThreadUnsafe(tuple, rel)
                    case Denotation.Latticenal(_bot, leq, _, _) =>
                        let len = Vector.length(terms);
                        let evalTerms = Vector.map(evalTerm(env, norm), terms);
                        let key = Vector.take(len - 1, evalTerms);
                        let latTerms = Vector.drop(len - 1, evalTerms);
                        let latTerm = match Vector.head(latTerms) {
                            case None => bug!("Found predicate without terms")
                            case Some(hd) => hd
                        };
                        let leqWrap = 
                            l1 -> l2 -> 
                                Normalization.unNormalizeReal(l1, index, norm) `leq` Normalization.unNormalizeReal(l2, index, norm);
                        not (latTerm `leqWrap` BPlusTree.getWithDefault(key, 0i64, rel))
                        // TODO: Ensure that bot maps to 0.
                        // not (latTerm `leqWrap` MutMap.getWithDefault(key, bot, rel))
                }
            case BoolExp.Eq(lhs, rhs) => evalTerm(env, norm, lhs) == evalTerm(env, norm, rhs)
            case BoolExp.Leq(leq, lhs, rhs, i) =>
                let boxed1 = Normalization.unNormalizeReal(evalTerm(env, norm, lhs), i, norm);
                let boxed2 = Normalization.unNormalizeReal(evalTerm(env, norm, rhs), i, norm);
                boxed1 `leq` boxed2
            case BoolExp.Guard0(f) => f()
            case BoolExp.Guard1(f, t, i) =>
                let evalT = evalTerm(env, norm);
                let v = evalT(t);
                let boxed = Normalization.unNormalizeReal(v, i, norm);
                f(boxed)
            case BoolExp.Guard2(f, t1, t2, i1, i2) =>
                let evalT = evalTerm(env, norm);
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let boxed1 = Normalization.unNormalizeReal(v1, i1, norm);
                let boxed2 = Normalization.unNormalizeReal(v2, i2, norm);
                f(boxed1)(boxed2)
            case BoolExp.Guard3(f, t1, t2, t3, i1, i2, i3) =>
                let evalT = evalTerm(env, norm);
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let boxed1 = Normalization.unNormalizeReal(v1, i1, norm);
                let boxed2 = Normalization.unNormalizeReal(v2, i2, norm);
                let boxed3 = Normalization.unNormalizeReal(v3, i3, norm);
                f(boxed1)(boxed2)(boxed3)
            case BoolExp.Guard4(f, t1, t2, t3, t4, i1, i2, i3, i4) =>
                let evalT = evalTerm(env, norm);
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let boxed1 = Normalization.unNormalizeReal(v1, i1, norm);
                let boxed2 = Normalization.unNormalizeReal(v2, i2, norm);
                let boxed3 = Normalization.unNormalizeReal(v3, i3, norm);
                let boxed4 = Normalization.unNormalizeReal(v4, i4, norm);
                f(boxed1)(boxed2)(boxed3)(boxed4)
            case BoolExp.Guard5(f, t1, t2, t3, t4, t5, i1, i2, i3, i4, i5) =>
                let evalT = evalTerm(env, norm);
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let v5 = evalT(t5);
                let boxed1 = Normalization.unNormalizeReal(v1, i1, norm);
                let boxed2 = Normalization.unNormalizeReal(v2, i2, norm);
                let boxed3 = Normalization.unNormalizeReal(v3, i3, norm);
                let boxed4 = Normalization.unNormalizeReal(v4, i4, norm);
                let boxed5 = Normalization.unNormalizeReal(v5, i5, norm);
                f(boxed1)(boxed2)(boxed3)(boxed4)(boxed5)
        })

    def evalTerm(env: SearchEnv[r], norm: Normalization[r], term: RamTerm): Int64 \ {r} = match term {
        case RamTerm.Lit(v) => v
        case RamTerm.LoadIndex(i) =>
            let (tupleEnv, _) = env;
            Vector.get(i, Array.get(i, tupleEnv))
        // case RamTerm.LoadLatVar(TupleVar.Named(i)) =>
        //     let (_, latEnv) = env;
        //     Array.get(i, latEnv)
        case RamTerm.Meet(cap, lhs, rhs, i) =>
            let boxed1 = Normalization.unNormalizeReal(evalTerm(env, norm, lhs), i, norm);
            let boxed2 = Normalization.unNormalizeReal(evalTerm(env, norm, rhs), i, norm);
            Normalization.normalizeBox(boxed1 `cap` boxed2, i, norm)
        case RamTerm.App0(f, i) =>
            Normalization.normalizeBox(f(), i, norm)
        case RamTerm.App1(f, t, i1, i_) =>
            let evalT = evalTerm(env, norm);
            let v = evalT(t); // Could make an eval that returns Boxed. Would be slightly more performant.
            let boxed1 = Normalization.unNormalizeReal(v, i1, norm);
            Normalization.normalizeBox(f(boxed1), i_, norm)
        case RamTerm.App2(f, t1, t2, i1, i2, i_) =>
            let evalT = evalTerm(env, norm);
            let v1 = evalT(t1);
            let v2 = evalT(t2);
            let boxed1 = Normalization.unNormalizeReal(v1, i1, norm);
            let boxed2 = Normalization.unNormalizeReal(v2, i2, norm);
            Normalization.normalizeBox(f(boxed1)(boxed2), i_, norm)
        case RamTerm.App3(f, t1, t2, t3, i1, i2, i3, i_) =>
            let evalT = evalTerm(env, norm);
            let v1 = evalT(t1);
            let v2 = evalT(t2);
            let v3 = evalT(t3);
            let boxed1 = Normalization.unNormalizeReal(v1, i1, norm);
            let boxed2 = Normalization.unNormalizeReal(v2, i2, norm);
            let boxed3 = Normalization.unNormalizeReal(v3, i3, norm);
            Normalization.normalizeBox(f(boxed1)(boxed2)(boxed3), i_, norm)
        case RamTerm.App4(f, t1, t2, t3, t4, i1, i2, i3, i4, i_) =>
            let evalT = evalTerm(env, norm);
            let v1 = evalT(t1);
            let v2 = evalT(t2);
            let v3 = evalT(t3);
            let v4 = evalT(t4);
            let boxed1 = Normalization.unNormalizeReal(v1, i1, norm);
            let boxed2 = Normalization.unNormalizeReal(v2, i2, norm);
            let boxed3 = Normalization.unNormalizeReal(v3, i3, norm);
            let boxed4 = Normalization.unNormalizeReal(v4, i4, norm);
            Normalization.normalizeBox(f(boxed1)(boxed2)(boxed3)(boxed4), i_, norm)
        case RamTerm.App5(f, t1, t2, t3, t4, t5, i1, i2, i3, i4, i5, i_) =>
            let evalT = evalTerm(env, norm);
            let v1 = evalT(t1);
            let v2 = evalT(t2);
            let v3 = evalT(t3);
            let v4 = evalT(t4);
            let v5 = evalT(t5);
            let boxed1 = Normalization.unNormalizeReal(v1, i1, norm);
            let boxed2 = Normalization.unNormalizeReal(v2, i2, norm);
            let boxed3 = Normalization.unNormalizeReal(v3, i3, norm);
            let boxed4 = Normalization.unNormalizeReal(v4, i4, norm);
            let boxed5 = Normalization.unNormalizeReal(v5, i5, norm);
            Normalization.normalizeBox(f(boxed1)(boxed2)(boxed3)(boxed4)(boxed5), i_, norm)
        // case RamTerm.RowLoad(rowVar, index) => bug!("Illegal RowLoad with ${rowVar} ${index}")
        case _ => bug!("Illegal term ${term}")
    }
}
