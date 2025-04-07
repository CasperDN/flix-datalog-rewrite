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

    pub type alias SearchEnv[r: Region] = (Array[SearchTuple[r], r], Array[Int64, r])


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
        if(Vector.isEmpty(tuples)) {
            index
        } else
    //         let totalSize = Vector.size(Vector.get(0, tuples));
    //         let notSearch = Array.empty(rc, searchLen - totalSize);
    //         Vector.foldLeft(counter -> i -> {
    // // TODO: Should be not Vector.memberOf(i, search), right? 
    //             if (Vector.memberOf(i, search)) {
    //                 Array.put(counter, i, notSearch);
    //                 counter + 1
    //             } else counter
    //         }, 0, Vector.range(0, totalSize));
            Vector.forEach(tuple -> {
                let (nonLat, lat, lub) = match toDenotation(relSym) {
                    case Denotation.Relational => (tuple, 0i64, a -> b -> 0i64)
                    case Denotation.Latticenal(_, _, lub, _) =>
                        let (vec1, vec2) = Vector.splitAt(Vector.length(tuple) - 1, tuple);
                        (vec1, Vector.get(0, vec2))
                };
                // let restOfTuple = Array.empty(rc, Vector.length(tuple) - searchLen);
                // Vector.forEach(i -> Array.put(Vector.get(i, nonLat), i, searchTuple), search);
                // Vector.forEach(i -> Array.put(Vector.get(i, nonLat), i, restOfTuple), search);
                // let map = MutMap.getOrElsePut(searchTuple, MutMap.empty(rc), index);
                BPlusTree.putWith(lubWith(index, norm, lub), nonLat, lat, index)
            }, tuples);
            index
        

    @Internal
    pub def _interpret(rc: Region[r], input: (RamProgram, Normalization[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
        let (program, norm) = input;
        let indexes = match program {
            case Program(_, facts, _, (indexMap, posMap)) => 
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
    pub def interpret(rc: Region[r], input: (RamProgram, Database[r], Normalization[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
        let (program, db, info) = input;
        // let db = MutMap.empty(rc);
        // match program {
        //     case RamProgram.Program(_, facts, predTrack, _) =>
        //         Map.forEach(id -> factSet -> {
        //             let sym = PredTrack.oldIDSymToRelSym(predTrack, id, PredTrack.PredType.Full);
        //             // let sym = unwrap(Map.get(id, predicateState));
        //             let mapForCurrent = MutMap.empty(rc);
        //             match sym {
        //                 case RelSym.Symbol(_, _, Denotation.Relational) => 
        //                     Vector.forEach(factTuple -> MutMap.put(factTuple, Reflect.default(), mapForCurrent), factSet)
        //                 case RelSym.Symbol(_, arity, Denotation.Latticenal(_, _, _, _)) => 
        //                     Vector.forEach(factTuple -> {
        //                         let nonLatticePart = Vector.slice({start=0}, {end=arity - 1}, factTuple);
        //                         let latticePart = Vector.get(arity - 1, factTuple);
        //                         MutMap.put(nonLatticePart, latticePart, mapForCurrent)
        //                     }, factSet)
        //             };
        //             // MutMap.put(id, mapForCurrent, db)
        //             MutMap.put(sym, mapForCurrent, db)
        //         }, facts)
        // };
        interpretWithDatabaseInternal(rc, db, info, program)
    


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
        case RamProgram.Program(stmt, _, predState, _) =>
            evalStmt(rc, db, norm, stmt);
            (marshallDb(rc, db, norm), predState)
    }


    def marshallDb(rc: Region[r], db: Database[r], norm: Normalization[r]): DatabaseExternal[r] = ???

    def evalStmt(rc: Region[r], db: Indexes[r], norm: Normalization[r], stmt: RamStmt): Unit \ r =
        match stmt {
            case RamStmt.Insert(relOp) => evalOp(rc, db, allocEnv(rc, 0, relOp), norm, relOp)
            case RamStmt.Merge(srcSym, dstSym, index) =>
            // let dst = Array.get(dstSym, db);
                let dst = MutMap.getOrElsePut(dstSym, MutMap.empty(rc), db);
                match toDenotation(srcSym) {
                    case Denotation.Relational =>
                        MutMap.merge(MutMap.getWithDefault(srcSym, MutMap.empty(rc), db), dst)
                    case Denotation.Latticenal(_, _, lub, _) =>
                        MutMap.mergeWith(lubWith(index, norm, lub), MutMap.getWithDefault(srcSym, MutMap.empty(rc), db), dst)
                }
            case RamStmt.Swap(lhs, rhs) =>
                let temp = MutMap.getWithDefault(lhs, MutMap.empty(rc), db);
                MutMap.put(lhs, MutMap.getWithDefault(rhs, MutMap.empty(rc), db), db);
                MutMap.put(rhs, temp, db)
            case RamStmt.Purge(ramSym) => MutMap.remove(ramSym, db)
            case RamStmt.Seq(stmts) => Vector.forEach(evalStmt(rc, db, norm), stmts)
            case RamStmt.Until(test, body) =>
                if (evalBoolExp(rc, db, (Array#{} @ rc, Array#{} @ rc), norm, test)) {
                    ()
                } else {
                    evalStmt(rc, db, norm, body);
                    evalStmt(rc, db, norm, stmt)
                }
            case RamStmt.Comment(_) => ()
            case RamStmt.Par(_) => ???
        }

    def allocEnv(rc: Region[r], depth: Int32, relOp: RelOp): SearchEnv[r] \ r = match relOp {
        case RelOp.Search(_, _, body)           => allocEnv(rc, depth + 1, body)
        case RelOp.SearchWithIndex(_, _, _, _, body)         => allocEnv(rc, depth + 1, body)
        case RelOp.Functional(_, _, _, body, _, _)    => allocEnv(rc, depth + 1, body)
        case RelOp.Project(_, _, _)                => (Array.repeat(rc, depth, Vector.empty()), Array.empty(rc, depth))
        case RelOp.If(_, then)                  => allocEnv(rc, depth, then)
    }

    def evalOp(rc: Region[r], db: Database[r], env: SearchEnv[r], info: Normalization.Normalization[r], op: RelOp): Unit \  r  =
        match op {
            case RelOp.Search(i, ramSym, body) =>
                let (tupleEnv, latEnv) = env;
                MutMap.forEach(t -> l -> {
                    Array.put(t, i, tupleEnv);
                    Array.put(l, i, latEnv);
                    evalOp(rc, db, env, info, body)
                }, MutMap.getWithDefault(ramSym, MutMap.empty(rc), db))
            case RelOp.SearchWithIndex(i, ramSym, qry, _, body) =>
                let (tupleEnv, latEnv) = env;
                let toSend = Vector.map(x -> match x {
                    // case QueryExp.Eq(RamTerm.RowLoad(tupleID, index), t2) => (index, t2)
                    case BoolExp.Eq(RamTerm.LoadIndex(index), t2) => (index, t2)
                    case BoolExp.Eq(t1, RamTerm.LoadIndex(index)) => (index, t1)
                    case _ => unchecked_cast(println("Hello ${Debug.stringify(x)}") as _ \ r); ???
                }, qry);
                MutMap.rangeQueryWith(evalQuery(env, info, Vector.toList(toSend)), t -> l -> {
                    Array.put(t, i, tupleEnv);
                    Array.put(l, i, latEnv);
                    evalOp(rc, db, env, info, body)
                }, MutMap.getWithDefault(ramSym, MutMap.empty(rc), db))
            case RelOp.Functional(i, f, terms, body, i1, _) =>
                let args = terms |> Vector.mapWithIndex(i_ -> x -> Normalization.unNormalizeReal(evalTerm(env, info, x), Vector.get(i_, i1), info));

                let result = Vector.map(vec -> Vector.mapWithIndex(i_ -> x -> Normalization.normalizeBox(x, Vector.get(i_, i1), info), vec), f(args));

                let (tupleEnv, _latEnv) = env; // TODO: Do we ever need to use latEnv?
                foreach (t <- result) {
                    Array.put(t, i, tupleEnv);
                    evalOp(rc, db, env, info, body)
                }
            case RelOp.Project(terms, ramSym, index) =>
                let rel = MutMap.getOrElsePut(ramSym, MutMap.empty(rc), db);
                match toDenotation(ramSym) {
                    case Denotation.Relational =>
                        let tuple = Vector.map(evalTerm(env, info), terms);
                        MutMap.put(tuple, Reflect.default(), rel)
                    case Denotation.Latticenal(bot, leq, lub, _) =>
                        // assume that length(terms) > 0
                        let len = Vector.length(terms);
                        let keyList = terms |> Vector.map(evalTerm(env, info));
                        let leqWrap = l1 -> l2 -> Normalization.unNormalizeReal(l1, index, info) `leq` l2;
                        let lubWrap = l1 -> l2 -> Normalization.normalizeBox(Normalization.unNormalizeReal(l1, index, info) `lub` Normalization.unNormalizeReal(l2, index, info), index, info);
                        let (key, latValList) = Vector.splitAt(len - 1, keyList);
                        let latVal = match Vector.head(latValList) {
                            case None => bug!("Found predicate without terms")
                            case Some(k) => k
                        };
                        if (latVal `leqWrap` bot) ()
                        else MutMap.putWith(lubWrap, key, latVal, rel)
                }
            case RelOp.If(test, then) =>
                if (evalBoolExp(rc, db, env, info, test)) {
                    evalOp(rc, db, env, info, then)
                } else {
                    ()
                }
            case _ => ()
        }

    def evalQuery(env: SearchEnv[r], info: Normalization.Normalization[r], qry: List[(Int32, RamTerm)], tuple: Vector[Int64]): Comparison \ r + r =
        match qry {
            case Nil => Comparison.EqualTo
            case (j, t) :: tl => match Vector.get(j, tuple) <=> evalTerm(env, info, t) {
                case Comparison.EqualTo => evalQuery(env, info, tl, tuple)
                case cmp => cmp
            }
        }

    def evalBoolExp(rc1: Region[r], db: Database[r], env: SearchEnv[r], info: Normalization.Normalization[r], es: Vector[BoolExp]): Bool \ r + r  =
        Vector.forAll(exp -> match exp {
            case BoolExp.IsEmpty(ramSym) =>
                MutMap.isEmpty(MutMap.getWithDefault(ramSym, MutMap.empty(rc1), db))
            case BoolExp.NotMemberOf(terms, ramSym, index) =>
                let rel = MutMap.getWithDefault(ramSym, MutMap.empty(rc1), db);
                match toDenotation(ramSym) {
                    case Denotation.Relational =>
                        let tuple = Vector.map(evalTerm(env, info), terms);
                        not MutMap.memberOf(tuple, rel)
                    case Denotation.Latticenal(_bot, leq, _, _) =>
                        let len = Vector.length(terms);
                        let evalTerms = Vector.map(evalTerm(env, info), terms);
                        let key = Vector.take(len - 1, evalTerms);
                        let latTerms = Vector.drop(len - 1, evalTerms);
                        let latTerm = match Vector.head(latTerms) {
                            case None => bug!("Found predicate without terms")
                            case Some(hd) => hd
                        };
                        let leqWrap = l1 -> l2 -> Normalization.unNormalizeReal(l1, index, info) `leq` Normalization.unNormalizeReal(l2, index, info);
                        not (latTerm `leqWrap` MutMap.getWithDefault(key, 0i64, rel))
                        // TODO: Ensure that bot maps to 0.
                        // not (latTerm `leqWrap` MutMap.getWithDefault(key, bot, rel))
                }
            case BoolExp.Eq(lhs, rhs) =>
                evalTerm(env, info, lhs) == evalTerm(env, info, rhs)
            case BoolExp.Leq(leq, lhs, rhs, i) =>
                let boxed1 = Normalization.unNormalizeReal(evalTerm(env, info, lhs), i, info);
                let boxed2 = Normalization.unNormalizeReal(evalTerm(env, info, rhs), i, info);
                boxed1 `leq` boxed2
            case BoolExp.Guard0(f) =>
                f()
            case BoolExp.Guard1(f, t, i) =>
                let evalT = evalTerm(env, info);
                let v = evalT(t);
                let boxed = Normalization.unNormalizeReal(v, i, info);
                f(boxed)
            case BoolExp.Guard2(f, t1, t2, i1, i2) =>
                let evalT = evalTerm(env, info);
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let boxed1 = Normalization.unNormalizeReal(v1, i1, info);
                let boxed2 = Normalization.unNormalizeReal(v2, i2, info);
                f(boxed1)(boxed2)
            case BoolExp.Guard3(f, t1, t2, t3, i1, i2, i3) =>
                let evalT = evalTerm(env, info);
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let boxed1 = Normalization.unNormalizeReal(v1, i1, info);
                let boxed2 = Normalization.unNormalizeReal(v2, i2, info);
                let boxed3 = Normalization.unNormalizeReal(v3, i3, info);
                f(boxed1)(boxed2)(boxed3)
            case BoolExp.Guard4(f, t1, t2, t3, t4, i1, i2, i3, i4) =>
                let evalT = evalTerm(env, info);
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let boxed1 = Normalization.unNormalizeReal(v1, i1, info);
                let boxed2 = Normalization.unNormalizeReal(v2, i2, info);
                let boxed3 = Normalization.unNormalizeReal(v3, i3, info);
                let boxed4 = Normalization.unNormalizeReal(v4, i4, info);
                f(boxed1)(boxed2)(boxed3)(boxed4)
            case BoolExp.Guard5(f, t1, t2, t3, t4, t5, i1, i2, i3, i4, i5) =>
                let evalT = evalTerm(env, info);
                let v1 = evalT(t1);
                let v2 = evalT(t2);
                let v3 = evalT(t3);
                let v4 = evalT(t4);
                let v5 = evalT(t5);
                let boxed1 = Normalization.unNormalizeReal(v1, i1, info);
                let boxed2 = Normalization.unNormalizeReal(v2, i2, info);
                let boxed3 = Normalization.unNormalizeReal(v3, i3, info);
                let boxed4 = Normalization.unNormalizeReal(v4, i4, info);
                let boxed5 = Normalization.unNormalizeReal(v5, i5, info);
                f(boxed1)(boxed2)(boxed3)(boxed4)(boxed5)
        }, es)

    def evalTerm(env: SearchEnv[r], info: Normalization.Normalization[r], term: RamTerm): Int64 \ {r} = match term {
        case RamTerm.Lit(v) => v
        case RamTerm.LoadIndex(i) =>
            let (tupleEnv, _) = env;
            Vector.get(i, Array.get(i, tupleEnv))
        // case RamTerm.LoadLatVar(TupleVar.Named(i)) =>
        //     let (_, latEnv) = env;
        //     Array.get(i, latEnv)
        case RamTerm.Meet(cap, lhs, rhs, i) =>
            let boxed1 = Normalization.unNormalizeReal(evalTerm(env, info, lhs), i, info);
            let boxed2 = Normalization.unNormalizeReal(evalTerm(env, info, rhs), i, info);
            Normalization.normalizeBox(boxed1 `cap` boxed2, i, info)
        case RamTerm.App0(f, i) =>
            Normalization.normalizeBox(f(), i, info)
        case RamTerm.App1(f, t, i1, i_) =>
            let evalT = evalTerm(env, info);
            let v = evalT(t); // Could make an eval that returns Boxed. Would be slightly more performant.
            let boxed1 = Normalization.unNormalizeReal(v, i1, info);
            Normalization.normalizeBox(f(boxed1), i_, info)
        case RamTerm.App2(f, t1, t2, i1, i2, i_) =>
            let evalT = evalTerm(env, info);
            let v1 = evalT(t1);
            let v2 = evalT(t2);
            let boxed1 = Normalization.unNormalizeReal(v1, i1, info);
            let boxed2 = Normalization.unNormalizeReal(v2, i2, info);
            Normalization.normalizeBox(f(boxed1)(boxed2), i_, info)
        case RamTerm.App3(f, t1, t2, t3, i1, i2, i3, i_) =>
            let evalT = evalTerm(env, info);
            let v1 = evalT(t1);
            let v2 = evalT(t2);
            let v3 = evalT(t3);
            let boxed1 = Normalization.unNormalizeReal(v1, i1, info);
            let boxed2 = Normalization.unNormalizeReal(v2, i2, info);
            let boxed3 = Normalization.unNormalizeReal(v3, i3, info);
            Normalization.normalizeBox(f(boxed1)(boxed2)(boxed3), i_, info)
        case RamTerm.App4(f, t1, t2, t3, t4, i1, i2, i3, i4, i_) =>
            let evalT = evalTerm(env, info);
            let v1 = evalT(t1);
            let v2 = evalT(t2);
            let v3 = evalT(t3);
            let v4 = evalT(t4);
            let boxed1 = Normalization.unNormalizeReal(v1, i1, info);
            let boxed2 = Normalization.unNormalizeReal(v2, i2, info);
            let boxed3 = Normalization.unNormalizeReal(v3, i3, info);
            let boxed4 = Normalization.unNormalizeReal(v4, i4, info);
            Normalization.normalizeBox(f(boxed1)(boxed2)(boxed3)(boxed4), i_, info)
        case RamTerm.App5(f, t1, t2, t3, t4, t5, i1, i2, i3, i4, i5, i_) =>
            let evalT = evalTerm(env, info);
            let v1 = evalT(t1);
            let v2 = evalT(t2);
            let v3 = evalT(t3);
            let v4 = evalT(t4);
            let v5 = evalT(t5);
            let boxed1 = Normalization.unNormalizeReal(v1, i1, info);
            let boxed2 = Normalization.unNormalizeReal(v2, i2, info);
            let boxed3 = Normalization.unNormalizeReal(v3, i3, info);
            let boxed4 = Normalization.unNormalizeReal(v4, i4, info);
            let boxed5 = Normalization.unNormalizeReal(v5, i5, info);
            Normalization.normalizeBox(f(boxed1)(boxed2)(boxed3)(boxed4)(boxed5), i_, info)
        // case RamTerm.RowLoad(rowVar, index) => bug!("Illegal RowLoad with ${rowVar} ${index}")
        case _ => bug!("Illegal term ${term}")
    }
}
