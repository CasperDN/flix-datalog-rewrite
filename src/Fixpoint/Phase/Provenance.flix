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

 mod Fixpoint.Phase.Provenance {
    use Fixpoint.Ast.Ram
    use Fixpoint.Ast.Ram.{RamProgram, RamStmt, RelOp, RamTerm, RelSym, arityOf, RowVar, RamId, BoolExp}
    use Fixpoint.Boxed.BoxedInt64
    use Fixpoint.Counter

    ///
    /// Augments `program` with `ProvMax` 
    ///
    @Internal
    pub def augmentProgram(withProv: Bool, program: RamProgram): RamProgram = 
        if (not withProv) program
        else augmentProgramInternal(program)
    
    def augmentProgramInternal(program: RamProgram): RamProgram = match program {
        case RamProgram.Program(stmt, facts, predicates, indexInfo) => region rc {
            let augmentedFacts = facts |> 
                Map.map(Vector.map(tuple -> Vector.append(tuple, Vector#{BoxedInt64(0i64), BoxedInt64(-1i64)})));
            let counter = Counter.fresh(rc);
            let maxId = getMaxIdStmt(0, stmt);
            Counter.set(maxId + 1, counter);
            let augmentedStmt = augmentStmt(counter, stmt);
            RamProgram.Program(augmentedStmt, augmentedFacts, predicates, indexInfo) |>
            Fixpoint.Debugging.notifyPreLowering("Provenance")
        }
    }

    ///
    /// Augments `RelOp`'s in `stmt` with `ProvMax` terms.
    ///
    def augmentStmt(counter: Counter[r], stmt: RamStmt): RamStmt \ r= match stmt {
        case RamStmt.Insert(op) => augmentOp(counter, Nil, op) |> RamStmt.Insert
        case RamStmt.MergeInto(_, _) => stmt
        case RamStmt.Swap(_, _) => stmt
        case RamStmt.Purge(_) => stmt
        case RamStmt.Seq(stmts) => Vector.map(augmentStmt(counter), stmts) |> RamStmt.Seq
        case RamStmt.Par(stmts) => Vector.map(augmentStmt(counter), stmts) |> RamStmt.Par
        case RamStmt.Until(bools, rest) => RamStmt.Until(bools, augmentStmt(counter, rest))
        case RamStmt.Comment(_) => stmt
        case RamStmt.EstimateJoinSize(_, _, _, _) => stmt
    }

    ///
    /// Augments `op` with `ProvMax` terms.
    ///
    def augmentOp(counter: Counter[r], rowVarsArity: List[(RowVar, Int32)], op: RelOp): RelOp \ r = match op {   
        case RelOp.Search(rowVar, relSym, body) => 
            augmentOp(counter, (rowVar, arityOf(relSym)) :: rowVarsArity, body) |> 
            RelOp.Search(rowVar, relSym)
        case RelOp.Query(rowVar, relSym, bools, index, body) => 
            augmentOp(counter, (rowVar, arityOf(relSym)) :: rowVarsArity, body) |>
            RelOp.Query(rowVar, relSym, bools, index)
        case RelOp.Functional(_, _, _, _, _) => 
            bug!("In Fixpoint.Phase.Provenance.augmentOp: Cannot do provenance with functional")
        case RelOp.Project(terms, relSym, ruleNum) =>
            let newTerms = Vector.append(
                terms,
                Vector#{
                    RamTerm.ProvMax(List.toVector(rowVarsArity)),
                    RamTerm.Lit(BoxedInt64(Int32.toInt64(ruleNum)), RamId.Id(-1))
                }
            );
            RelOp.Project(newTerms, relSym, ruleNum)
        case RelOp.If(boolExps, body) =>  
            augmentOp(counter, rowVarsArity, body) |> RelOp.If(boolExps)
    }
    
    ///
    /// Returns the maximum id in `stmt` given the current maximum id `max`.
    ///
    /// Unfortunately, this requires an almost complete Ast pass.
    ///
    def getMaxIdStmt(max: Int32, stmt: RamStmt): Int32 = match stmt {
        case RamStmt.Insert(op) => getMaxIdOp(max, op)
        case RamStmt.MergeInto(_, _) => max
        case RamStmt.Swap(_, _) => max
        case RamStmt.Purge(_) => max
        case RamStmt.Seq(stmts) => Vector.foldLeft(getMaxIdStmt, max, stmts)
        case RamStmt.Par(stmts) => Vector.foldLeft(getMaxIdStmt, max, stmts)
        case RamStmt.Until(bools, rest) => 
            getMaxIdStmt(Vector.foldLeft(getMaxIdBoolExp, max, bools), rest)
        case RamStmt.Comment(_) => max
        case RamStmt.EstimateJoinSize(_, _, _, _) => max
    }

    def getMaxIdOp(max: Int32, op: RelOp): Int32 = match op {
        case RelOp.Search(RowVar.Named(i), _, body) => 
            getMaxIdOp(Int32.max(max, i), body)
        case RelOp.Query(RowVar.Named(i), _, bools, _, body) => 
            let acc = getMaxIdOp(Int32.max(max, i), body);
            getMaxIdOp(Vector.foldLeft(getMaxIdBoolExp, acc, bools), body)
        case RelOp.Functional(RowVar.Named(i), _, terms, body, _) =>
            getMaxIdOp(Vector.foldLeft(getMaxIdTerm, Int32.max(max, i), terms), body)
        case RelOp.Project(terms, _, _) => 
            Vector.foldLeft(getMaxIdTerm, max, terms)
        case RelOp.If(bools, body) => 
            getMaxIdOp(Vector.foldLeft(getMaxIdBoolExp, max, bools), body)
    }

    def getMaxIdBoolExp(max: Int32, bool: BoolExp): Int32 = match bool {
        case BoolExp.Not(boolExp) => getMaxIdBoolExp(max, boolExp)
        case BoolExp.IsEmpty(_) => max
        case BoolExp.NotMemberOf(terms, _) => 
            Vector.foldLeft(getMaxIdTerm, max, terms)
        case BoolExp.NotBot(term, _, _) => getMaxIdTerm(max, term)
        case BoolExp.Leq(_, RowVar.Named(i), _) => Int32.max(i, max)
        case BoolExp.Eq(t1, t2) => getMaxIdTerm(getMaxIdTerm(max, t1), t2)
        case BoolExp.Guard1(_, t) => getMaxIdTerm(max, t)
        case BoolExp.Guard2(_, t1, t2) => 
            Vector#{t1, t2} |> Vector.foldLeft(getMaxIdTerm, max)
        case BoolExp.Guard3(_, t1, t2, t3) => 
            Vector#{t1, t2, t3} |> Vector.foldLeft(getMaxIdTerm, max)
        case BoolExp.Guard4(_, t1, t2, t3, t4) => 
            Vector#{t1, t2, t3, t4} |> Vector.foldLeft(getMaxIdTerm, max)
        case BoolExp.Guard5(_, t1, t2, t3, t4, t5) => 
            Vector#{t1, t2, t3, t4, t5} |> Vector.foldLeft(getMaxIdTerm, max)
    }

    def getMaxIdTerm(max: Int32, term: RamTerm): Int32 = match Ram.getTermRamId(term) {
        case RamId.Id(i) => Int32.max(max, i)
        case _ => max
    }

 }