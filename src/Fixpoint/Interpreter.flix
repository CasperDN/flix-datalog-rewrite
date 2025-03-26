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


// mod Fixpoint.Database2 {

// }

mod Fixpoint.Interpreter {
    use Fixpoint.Normalization
    use Fixpoint.Normalization.ObjectMarshallingInfo
    use PredTrack.PredSymMapInternal
    use Fixpoint.Boxed;

    use Fixpoint.Ast.ExecutableRam.{RamStmt, RelOp, RamTerm, BoolExp, TupleVar, RamProgram}
    use Fixpoint.Ast.AugmentedRam.{RelSym, toDenotation}
    use Fixpoint.Ast.Shared.Denotation
    use Fixpoint.Normalization
    // use PredTrack


    pub type alias Database[r: Region] = MutMap[RelSym, MutMap[Vector[Int64], Int64, r], r]

    pub type alias DatabaseExternal[r: Region] = MutMap[RelSym, MutMap[Vector[Boxed], Boxed, r], r]

    pub type alias SearchEnv[r: Region] = (Array[Vector[Int64], r], Array[Int64, r])

    // pub type alias MetaData[r: Eff] = (Normalization.ObjectMarshallingInfo[r], Bool)

    // pub type alias Database[v: Type, r: Region] = MutMap[Int64, MutMap[Vector, v, r], r]

    // pub type alias Database[v: Type, r: Region] = MutMap[RelSym, MutMap[Vector, v, r], r]

    // /**
    // pub type alias Database[r: Region] = (
    //     MutMap[Int64, MutSet[Vector, r], r], 
    //     MutMap[Int64, MutMap[Vector, r], r]
    // )
    //  */


    // /**
    // pub type alias Database[r: Region] = {
    //     // (longMaps = MutMap[RelSym, MutMap[Vector[Int64]]],)        
    //     )
        
    // }

    //  */


    @Internal
    pub def interpret(rc: Region[r], input: (RamProgram, Database[r], ObjectMarshallingInfo[r])): (DatabaseExternal[r], PredSymMapInternal) \ r =
        let (program, db, info) = input;
        // let db = MutMap.empty(rc);
        match program {
            case RamProgram.Program(_, facts, predTrack, _) =>
                Map.forEach(id -> factSet -> {
                    let sym = PredTrack.oldIDSymToRelSym(predTrack, id, PredTrack.PredType.Full);
                    // let sym = unwrap(Map.get(id, metaInformation));
                    let mapForCurrent = MutMap.empty(rc);
                    match sym {
                        case RelSym.Symbol(_, _, Denotation.Relational) => 
                            Vector.forEach(factTuple -> MutMap.put(factTuple, Reflect.default(), mapForCurrent), factSet)
                        case RelSym.Symbol(_, arity, Denotation.Latticenal(_, _, _, _)) => 
                            Vector.forEach(factTuple -> {
                                let nonLatticePart = Vector.slice({start=0}, {end=arity - 1}, factTuple);
                                let latticePart = Vector.get(arity - 1, factTuple);
                                MutMap.put(nonLatticePart, latticePart, mapForCurrent)
                            }, factSet)
                    };
                    // MutMap.put(id, mapForCurrent, db)
                    MutMap.put(sym, mapForCurrent, db)
                }, facts)
        };
        interpretWithDatabaseInternal(rc, db, info, program)
    


    @Internal
    pub def interpretWithDatabase(rc: Region[r], input: (Database[r], ObjectMarshallingInfo[r], RamProgram)): (DatabaseExternal[r], PredSymMapInternal) \ r = 
    let (db, info, program) = input;
    interpretWithDatabaseInternal(rc, db, info, program)

    @Internal
    pub def interpretWithDatabaseInternal(rc: Region[r], db: Database[r], info: ObjectMarshallingInfo[r], program: RamProgram): (DatabaseExternal[r], PredSymMapInternal) \ r = match Fixpoint.Debugging.notifyPreInterpret(program) {
        case RamProgram.Program(stmt, _, meta, _) =>
            evalStmt(rc, db, info, stmt);
            (marshallDb(rc, db, info), meta)
    }

    def marshallDb(rc: Region[r], db: Database[r], info: ObjectMarshallingInfo[r]): DatabaseExternal[r] = ???

    def evalStmt(rc: Region[r], db: Database[r], info: ObjectMarshallingInfo[r], stmt: RamStmt): Unit \ r =
        match stmt {
            case RamStmt.Insert(relOp) => evalOp(rc, db, allocEnv(rc, 0, relOp), info, relOp)
            case RamStmt.Merge(srcSym, dstSym, index) =>
                let dst = MutMap.getOrElsePut(dstSym, MutMap.empty(rc), db);
                match toDenotation(srcSym) {
                    case Denotation.Relational =>
                        MutMap.merge(MutMap.getWithDefault(srcSym, MutMap.empty(rc), db), dst)
                    case Denotation.Latticenal(_, _, lub, _) =>
                        // Normalization.;
                        let lubWrap = l1 -> l2 -> Normalization.normalizeBox(Normalization.unNormalizeReal(l1, index, info) `lub` Normalization.unNormalizeReal(l2, index, info), index, info);
                        MutMap.mergeWith(lubWrap, MutMap.getWithDefault(srcSym, MutMap.empty(rc), db), dst)
                }
            case RamStmt.Swap(lhs, rhs) =>
                let temp = MutMap.getWithDefault(lhs, MutMap.empty(rc), db);
                MutMap.put(lhs, MutMap.getWithDefault(rhs, MutMap.empty(rc), db), db);
                MutMap.put(rhs, temp, db)
            case RamStmt.Purge(ramSym) => MutMap.remove(ramSym, db)
            case RamStmt.Seq(stmts) => Vector.forEach(evalStmt(rc, db, info), stmts)
            case RamStmt.Until(test, body) =>
                if (evalBoolExp(rc, db, (Array#{} @ rc, Array#{} @ rc), info, test)) {
                    ()
                } else {
                    evalStmt(rc, db, info, body);
                    evalStmt(rc, db, info, stmt)
                }
            case RamStmt.Comment(_) => ()
            case RamStmt.Par(_) => ???
        }

    def allocEnv(rc: Region[r], depth: Int32, relOp: RelOp): SearchEnv[r] \ r = match relOp {
        case RelOp.Search(_, _, body)           => allocEnv(rc, depth + 1, body)
        case RelOp.SearchWithIndex(_, _, _, body)         => allocEnv(rc, depth + 1, body)
        case RelOp.Functional(_, _, _, body, _)    => allocEnv(rc, depth + 1, body)
        case RelOp.Project(_, _, _)                => (Array.repeat(rc, depth, Vector.empty()), Array.empty(rc, depth))
        case RelOp.If(_, then)                  => allocEnv(rc, depth, then)
    }

    def evalOp(rc1: Region[r], db: Database[r], env: SearchEnv[r], info: Normalization.ObjectMarshallingInfo[r], op: RelOp): Unit \  r + r  =
        match op {
            case RelOp.Search(TupleVar.Named(i), ramSym, body) =>
                let (tupleEnv, latEnv) = env;
                MutMap.forEach(t -> l -> {
                    Array.put(t, i, tupleEnv);
                    Array.put(l, i, latEnv);
                    evalOp(rc1, db, env, info, body)
                }, MutMap.getWithDefault(ramSym, MutMap.empty(rc1), db))
            case RelOp.SearchWithIndex(TupleVar.Named(i), ramSym, qry, body) =>
                let (tupleEnv, latEnv) = env;
                let toSend = Vector.map(x -> match x {
                    // case QueryExp.Eq(RamTerm.RowLoad(tupleID, index), t2) => (index, t2)
                    // case BoolExp.Eq(RamTerm.RowLoad(_, index), t2) => (index, t2)
                    case BoolExp.Eq(RamTerm.LoadIndex(index), t2) => (index, t2)
                    case _ => ???
                }, qry);
                MutMap.rangeQueryWith(evalQuery(env, info, Vector.toList(toSend)), t -> l -> {
                    Array.put(t, i, tupleEnv);
                    Array.put(l, i, latEnv);
                    evalOp(rc1, db, env, info, body)
                }, MutMap.getWithDefault(ramSym, MutMap.empty(rc1), db))
            case RelOp.Functional(TupleVar.Named(i), f, terms, body, i1) =>
                let args = terms |> Vector.mapWithIndex(i_ -> x -> Normalization.unNormalizeReal(evalTerm(env, info, x), Vector.get(i_, i1), info));

                let result = Vector.map(vec -> Vector.mapWithIndex(i_ -> x -> Normalization.normalizeBox(x, Vector.get(i_, i1), info), vec), f(args));

                let (tupleEnv, _latEnv) = env; // TODO: Do we ever need to use latEnv?
                foreach (t <- result) {
                    Array.put(t, i, tupleEnv);
                    evalOp(rc1, db, env, info, body)
                }
            case RelOp.Project(terms, ramSym, index) =>
                let rel = MutMap.getOrElsePut(ramSym, MutMap.empty(rc1), db);
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
                if (evalBoolExp(rc1, db, env, info, test)) {
                    evalOp(rc1, db, env, info, then)
                } else {
                    ()
                }
            case _ => ()
        }

    def evalQuery(env: SearchEnv[r], info: Normalization.ObjectMarshallingInfo[r], qry: List[(Int32, RamTerm)], tuple: Vector[Int64]): Comparison \ r + r =
        match qry {
            case Nil => Comparison.EqualTo
            case (j, t) :: tl => match Vector.get(j, tuple) <=> evalTerm(env, info, t) {
                case Comparison.EqualTo => evalQuery(env, info, tl, tuple)
                case cmp => cmp
            }
        }

    def evalBoolExp(rc1: Region[r], db: Database[r], env: SearchEnv[r], info: Normalization.ObjectMarshallingInfo[r], es: Vector[BoolExp]): Bool \ r + r  =
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

    def evalTerm(env: SearchEnv[r], info: Normalization.ObjectMarshallingInfo[r], term: RamTerm): Int64 \ {r, r} = match term {
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

    // def unwrap(o: Option[a]): a = match o {
    //     case Some(a) => a
    //     case None => bug!("Unexpected None in Interpreter")
    // }

    // def evalInputFacts(rc: Region[r], term: RamTerm): v \ r = 
    //     let arr0 = Array.empty(rc, 0);
    //     let arr = Array.empty(rc, 0);
    //     evalTerm((arr0, arr), term)

}
