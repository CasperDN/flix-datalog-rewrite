/*
 * Copyright 2025 Casper Dalgaard Nielsen
 *                Adam Yasser Tallouzi
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

// Constraint: If an outgoing functional `VarSym` it must dynamically be assigned a type, later.

mod Fixpoint.TypeInfo {
    use Fixpoint.Ast.Datalog.{BodyPredicate, BodyTerm, Datalog, Constraint, HeadPredicate, HeadTerm, VarSym}
    use Fixpoint.Ast.Datalog.Datalog.Datalog
    use Fixpoint.Ast.Ram.{RamProgram, RelSym, Predicates}
    use Fixpoint.Ast.Shared.PredSym
    use Fixpoint.Ast.Shared.PredSym.PredSym
    use Fixpoint.Boxed
    use Fixpoint.Counter
    // use Fixpoint.Predicate
    use Fixpoint.Predicate.{allFullRelSyms, getMax}
    use Fixpoint.Util.getOrCrash


    @Internal
    pub type alias Types = Vector[Int32]

    @Internal
    pub type alias TypeInformation = Vector[Types]

    type alias UnificationType[r: Region] = MutDisjointSets[(Int64, Int32), r]

    type alias VarSymUnifier[r: Region] = MutMap[String, (Int64, Int32), r]

    type alias PseudoStrataOrder[r: Region] = MutMap[Int32, MutMap[Int32, List[(Int32, Constraint)], r], r]

    def toInt32(i: Int64): Int32 = getOrCrash(Int64.tryToInt32(i))

    pub def provType(): Int32 = 0

    @Internal
    pub def typeDatalog(d: Datalog, pseudoStratums: PseudoStrataOrder[r], predicates: Predicates, withProv: Bool): TypeInformation \ r = match d {
        case Datalog(_, _) => region rc {
            let idCreator = Counter.fresh(rc);
            // Ensure that the first index is 1.
            let rels = allFullRelSyms(predicates);
            let relNum = getOrCrash(Int64.tryToInt32(getMax(predicates)));
            // The first functional will get an id 1 greater than the largest PredSym.
            Counter.set(relNum, idCreator);
            let typeUnifier = MutDisjointSets.empty(rc);
            // Have to traverse in same order as `Compuler.flix`
            // Vector.forEach(rule -> typeConstraint(rule, typeUnifier, idCreator), rules);
            foreach ((_, pseudStrat) <- pseudoStratums) {
                MutMap.foldLeft(_ -> rules2 -> {
                    List.forEach(match (_, rule) -> typeConstraint(rule, typeUnifier, idCreator), rules2)
                }, (), pseudStrat)
            };


            let maxId = Counter.get(idCreator);
            let arr = Array.empty(rc, maxId);
            foreach(RelSym.Symbol(PredSym(_, id), arity, _) <- rels) {
                // let safeArity = if (not withProv) {
                //     arity
                // } else {
                //     arity + 2
                // };
                // Array.put(Array.repeat(rc, safeArity, -1), toInt32(id), arr)
                Array.put(Array.repeat(rc, arity, -1), toInt32(id), arr)
            };
            // Register functionals.
            foreach (id <- Vector.range(relNum, maxId)) {
                let arity = computeSizeOfFunctional(Int32.toInt64(id), 0, typeUnifier);
                Array.put(Array.repeat(rc, arity, -1), id, arr)
            };

            let typeCreator = Counter.fresh(rc);
            if (withProv) {
                // Set the 2 last values of the type to be provenance types.
                // Array.forEach(array -> {
                //     let len = Array.length(array);
                //     Array.put(0, len - 1, array);
                //     Array.put(0, len - 2, array)
                // }, arr);
                // Reserve position 0 for provenance values.
                Counter.increment(typeCreator)
            } else {
                ()
            };
            foreach (id <- Vector.range(0, maxId)) {
                let curArr = Array.get(id, arr);
                foreach (index <- Vector.range(0, Array.length(curArr))) match MutDisjointSets.find((Int32.toInt64(id), index), typeUnifier) {
                    case None => Array.put(Counter.getAndIncrement(typeCreator), index, curArr)
                    case Some((id2Int64, index2)) =>
                        let id2 = toInt32(id2Int64);
                        let otherArr = Array.get(id2, arr);
                        match Array.get(index2, otherArr) {
                            case -1 =>
                                let newType = Counter.getAndIncrement(typeCreator);
                                Array.put(newType, index2, otherArr);
                                Array.put(newType, index, curArr)
                            case someType =>
                                Array.put(someType, index, curArr)
                        }
                }
            };
            // foreach (RelSym.Symbol(PredSym(_, id), arity, _) <- rels) {
            //     let curArr = Array.get(toInt32(id), arr);
            //     foreach (index <- Vector.range(0, arity)) match MutDisjointSets.find((id, index), typeUnifier) {
            //         case None => Array.put(Counter.getAndIncrement(typeCreator), index, curArr)
            //         case Some((id2Int64, index2)) =>
            //             let id2 = toInt32(id2Int64);
            //             let otherArr = Array.get(id2, arr);
            //             match Array.get(index2, otherArr) {
            //                 case -1 =>
            //                     let newType = Counter.getAndIncrement(typeCreator);
            //                     Array.put(newType, index2, otherArr);
            //                     Array.put(newType, index, curArr)
            //                 case someType =>
            //                     Array.put(someType, index, curArr)
            //             }
            //     }
            // };
            // // Fix the functionals
            // foreach (id <- Vector.range(relNum, maxId)) {
            //     typeFunctional(id, 0, rc, MutList.empty(rc), typeCreator, arr, typeUnifier)
            // };            
            // Don't copy arrays, just cast them.
            unchecked_cast(arr as Vector[Vector[Int32]])
        }
        case _ => unreachable!()
    }

    pub def expandTypeInfoToProv(typeInfo: TypeInformation, predicates: Predicates): TypeInformation =
        let max = getMax(predicates);
        Vector.mapWithIndex(i -> v -> match Int32.toInt64(i) < max {
            case true => expandTypeToProv(v)
            case false => v
        }, typeInfo)


    pub def expandTypeToProv(type_: Types): Types = type_ ++ Vector#{provType(), provType()}


    def computeSizeOfFunctional(id: Int64, count: Int32, typeUnifier: UnificationType[r]): Int32 \ r =
        match MutDisjointSets.find((id, count), typeUnifier) {
            case None => count
            case Some(_) => computeSizeOfFunctional(id, count + 1, typeUnifier)
        }

    // def typeFunctional(id: Int32, curIndex: Int32, rc: Region[r], mutList: MutList[Int32, r], typeCreator: Counter[r], arr: Array[Array[Int32, r], r], typeUnifier: UnificationType[r]): Unit \ r = {
    //     match MutDisjointSets.find((Int32.toInt64(id), curIndex), typeUnifier) {
    //         // Save the built type.
    //         case None => Array.put(MutList.toArray(rc, mutList), id, arr)
    //         // Append a type to `mutList`
    //         case Some((id2Int64, index2)) =>
    //             unchecked_cast(println(id) as _ \ r);
    //             let id2 = toInt32(id2Int64);
    //             let otherArr = Array.get(id2, arr);
    //             match Object.isNull(otherArr) {
    //                 case true =>
    //                     MutList.push(someType, mutList)
    //                 case false =>
    //             };
    //             match Array.get(index2, otherArr) {
    //                 case -1 =>
    //                     let newType = Counter.getAndIncrement(typeCreator);
    //                     Array.put(newType, index2, otherArr);
    //                     MutList.push(newType, mutList)
    //                 case someType =>
    //                     MutList.push(someType, mutList)
    //             }
    //     }
    // }

    @Internal
    pub def getType(id: Int64, index: Int32, typeInfo: TypeInformation): Int32 = {
        Vector.get(index, Vector.get(toInt32(id), typeInfo))
    }

    @Internal
    pub def getTypeOf(id: Int64, typeInfo: TypeInformation): Vector[Int32] = {
        Vector.get(toInt32(id), typeInfo)
    }

    def typeConstraint(rule: Constraint, typeUnifier: UnificationType[r], counter: Counter[r]): Unit \ r = match rule {
        case Constraint.Constraint(HeadPredicate.HeadAtom(PredSym(_, id), _, headTerms), body) => region rc {
            let varSymUnifier = MutMap.empty(rc);
            typeHead(id, headTerms, varSymUnifier, typeUnifier);
            Vector.forEach(bodyPred -> typeBodyPred(bodyPred, varSymUnifier, typeUnifier, counter), body)
        }
    }

    def typeHead(id: Int64, terms: Vector[HeadTerm], varSymUnifier: VarSymUnifier[r1], typeUnifier: UnificationType[r2]): Unit \ r1 + r2 =
        foreach((i, t) <- ForEach.withIndex(terms)) {
            match t {
                case HeadTerm.Var(VarSym.VarSym(sym)) =>
                    typeVar(id, i, sym, varSymUnifier, typeUnifier)
                case _ => ()
            }
        }

    def typeVar(id: Int64, index: Int32, sym: String, varSymUnifier: VarSymUnifier[r1], typeUnifier: UnificationType[r2]): Unit \ r1 + r2 = {
        let (repId, repIndex) = MutMap.getOrElsePut(sym, (id, index), varSymUnifier);
        if(id == repId and repIndex == index) {
            // unchecked_cast(println(id) as _ \ r1);
            // unchecked_cast(println(index) as _ \ r1);
            // unchecked_cast(println(sym) as _ \ r1);
            MutDisjointSets.makeSet((repId, repIndex), typeUnifier)
        } else {
            MutDisjointSets.union((repId, repIndex), (id, index), typeUnifier)
        }
    }

    def typeBodyPred(bodyPred: BodyPredicate, varSymUnifier: VarSymUnifier[r1], typeUnifier: UnificationType[r2], counter: Counter[r2]): Unit \ r1 + r2 = match bodyPred {
        case BodyPredicate.BodyAtom(PredSym(_, id), _, _, _, terms) =>
            Vector.forEachWithIndex(index -> term -> typeBodyTerm(id, index, term, varSymUnifier, typeUnifier), terms)
        case BodyPredicate.Functional(outVars, _, _inVars) =>
            let id = Int32.toInt64(Counter.getAndIncrement(counter));
            Vector.forEachWithIndex(index -> match VarSym.VarSym(sym) -> typeVar(id, index, sym, varSymUnifier, typeUnifier), outVars)
        case _ => ()
    }

    def typeBodyTerm(id: Int64, index: Int32, term: BodyTerm, varSymUnifier: VarSymUnifier[r1], typeUnifier: UnificationType[r2]): Unit \ r1 + r2 = match term {
        case BodyTerm.Wild => ()
        case BodyTerm.Lit(_) => ()
        case BodyTerm.Var(VarSym.VarSym(sym)) => typeVar(id, index, sym, varSymUnifier, typeUnifier)
    }

}