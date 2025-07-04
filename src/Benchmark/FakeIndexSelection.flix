// /*
//  * Copyright 2025 Casper Dalgaard Nielsen
//  *                Adam Yasser Tallouzi
//  *
//  * Licensed under the Apache License, Version 2.0 (the "License");
//  * you may not use this file except in compliance with the License.
//  * You may obtain a copy of the License at
//  *
//  *   http://www.apache.org/licenses/LICENSE-2.0
//  *
//  * Unless required by applicable law or agreed to in writing, software
//  * distributed under the License is distributed on an "AS IS" BASIS,
//  * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
//  * See the License for the specific language governing permissions and
//  * limitations under the License.
//  */

// mod Fixpoint.Benchmark.FakeIndexSelection {
//     use Fixpoint.Ast.Ram.{RamStmt, RamProgram, RelOp, BoolExp, RelSym, RamTerm, Search, Indexes, IndexInformation, RowVar, arityOf, arityOfNonLat};
//     use Fixpoint.Predicates.{relSymFromPredType, relSymToPredType, PredType, relSymsOfProgram}
//     use Fixpoint.UniqueInts
    
//     type alias Searches[r: Eff] = MutMap[RelSym, List[Search], r]

//     pub def indexProgram(program: RamProgram): RamProgram = match program {
//         case RamProgram.Program(stmt, facts, meta, _) => 
//             let indexes = 
//                 relSymsOfProgram(program) |>
//                 List.foldLeft(acc -> relSym -> {
//                     Map.insert(relSym, Vector#{Vector.range(0, arityOfNonLat(relSym))}, acc)
//                 }, Map#{});
//             let (indexedStmt, indexPlacement) = region rc2 {
//                 let indexState = UniqueInts.empty(rc2);
//                 let indexedStmt = indexStmt(stmt, indexes, indexState);
//                 Map.forEach(relSym -> _ -> {
//                     UniqueInts.getIndex((relSym, 0), indexState);
//                     ()
//                 }, indexes);
//                 let finalState = UniqueInts.toMap(indexState);
//                 (indexedStmt, finalState)
//             };
//             RamProgram.Program(indexedStmt, facts, meta, (indexes, indexPlacement))
//     }

//     ///
//     /// Propagates the appropriate indexes to `Query` ops.
//     ///
//     def indexStmt(stmt: RamStmt, constructedIndexes: Indexes, indexState: UniqueInts[(RelSym, Int32), r]): RamStmt \ r = match stmt {
//         case RamStmt.Insert(op) => RamStmt.Insert(indexOp(op, constructedIndexes, indexState))
//         case RamStmt.MergeInto(_, _) => stmt
//         case RamStmt.Swap(_, _) => stmt
//         case RamStmt.Purge(_) => stmt
//         case RamStmt.Seq(xs) => RamStmt.Seq(Vector.map(x -> indexStmt(x, constructedIndexes, indexState), xs))
//         case RamStmt.Par(xs) => RamStmt.Par(Vector.map(x -> indexStmt(x, constructedIndexes, indexState), xs))
//         case RamStmt.Until(boolExps, body) => RamStmt.Until(boolExps, indexStmt(body, constructedIndexes, indexState))
//         case RamStmt.EstimateJoinSize(_, _, _, _) => bug!("Should not happen during testing of index selection")
//         case RamStmt.Comment(_) => stmt 
//     }

//     ///
//     /// Returns memory position of the index that uses `Search` for `RelSym`.
//     ///
//     def lookupIndex(
//         _relSym: RelSym, 
//         _search: Search,
//         _constructedIndexes: Indexes    
//     ): Int32 = 0

//     ///
//     /// Updates `Query` ops with their corresponding index location in memory.
//     ///
//     def indexOp(op: RelOp, constructedIndexes: Indexes, indexState: UniqueInts[(RelSym, Int32), r]): RelOp \ r = match op {
//         case RelOp.Search(rowVar, relSym, body) =>
//             RelOp.Search(rowVar, relSym, indexOp(body, constructedIndexes, indexState))
//         case RelOp.Query(rowVar, relSym, boolExps, _, body) => region rc {
//             let unusedBools = MutList.empty(rc);
//             let (_, eqs, _) = Vector.foldLeft(acc -> exp -> match exp {
//                     case BoolExp.Eq(RamTerm.RowLoad(rv, i, rel), other) if (rowVar == rv) => BoolExp.Eq(RamTerm.RowLoad(rv, i, rel), other) :: acc
//                     case BoolExp.Eq(other, RamTerm.RowLoad(rv, i, rel)) if (rowVar == rv) => BoolExp.Eq(RamTerm.RowLoad(rv, i, rel), other) :: acc
//                     case _ =>
//                         MutList.push(exp, unusedBools);
//                         acc
//                 }, List.empty(), boolExps) |>
//                 List.sortBy(eq -> match eq {
//                     case BoolExp.Eq(RamTerm.RowLoad(_, i, _), _) => i
//                     case _ => unreachable!()
//                 }) |>
//                 List.foldLeft(match (head, acc, continue) -> eq -> match eq {
//                     case BoolExp.Eq(RamTerm.RowLoad(_, i, _), _) => 
//                         if(not continue) {
//                             MutList.push(eq, unusedBools);
//                             (head, acc, continue)
//                         } else {
//                             if(i == head) {
//                                 MutList.push(eq, unusedBools);
//                                 (head, acc, continue)
//                             } else if (i == head + 1) {
//                                 (i, eq :: acc, true)
//                             } else {
//                                 MutList.push(eq, unusedBools);
//                                 (head, acc, false)
//                             }
//                         }
//                     case _ => unreachable!()
//                 }, (-1, Nil, true));
//             let search = eqs |>
//                 List.map(x -> match x {
//                     case BoolExp.Eq(RamTerm.RowLoad(_, i, _), _) => i
//                     case _ => unreachable!()
//                 }) |>
//                 List.toVector;
//             let index = lookupIndex(relSym, search, constructedIndexes);
//             let absoluteIndex = UniqueInts.getIndex((relSym, index), indexState);
//             let newBody =  RelOp.If(MutList.toVector(unusedBools), indexOp(body, constructedIndexes, indexState));
//             RelOp.Query(rowVar, relSym, List.toVector(eqs), absoluteIndex, newBody)
//         }
//         case RelOp.Functional(rowVar, func, terms, body, arity) =>
//             RelOp.Functional(rowVar, func, terms, indexOp(body, constructedIndexes, indexState), arity)
//         case RelOp.Project(_, _, _) => op
//         case RelOp.If(boolExps, body) => RelOp.If(boolExps, indexOp(body, constructedIndexes, indexState))
//     }

// }
