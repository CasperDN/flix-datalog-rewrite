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

mod Fixpoint.Helpers {
    use Fixpoint.Ast.Ram.{RamProgram, RowVar, RelSym, RamStmt, RelOp}

    @Internal
    pub def unwrap(x: Option[a]): a = match x {
        case Some(v) => v
        case None => ???
    }

    // Simple passes used by 2 phases

    ///
    /// Returns a list `(RowVar, RelSym)` in `program` in the order of the nesting.
    ///
    @Internal
    pub def collectRowVarRelSym(program: RamProgram): List[(RowVar, RelSym)] = match program {
        case RamProgram.Program(stmt, _, _, _) => 
            collectRowVarRelSymStmt(stmt)
    }

    ///
    /// Returns a list `(RowVar, RelSym)` in `stmt`.
    ///
    def collectRowVarRelSymStmt(stmt: RamStmt): List[(RowVar, RelSym)] \ r = match stmt {
        case RamStmt.Insert(op) => collectRowVarRelSymOp(op)
        case RamStmt.MergeInto(_, _) => Nil
        case RamStmt.Swap(_, _) => Nil
        case RamStmt.Purge(_) => Nil
        case RamStmt.Seq(stmts) => Vector.foldLeft(acc -> x -> List.append(collectRowVarRelSymStmt(x), acc), Nil, stmts)
        case RamStmt.Par(stmts) => Vector.foldLeft(acc -> x -> List.append(collectRowVarRelSymStmt(x), acc), Nil, stmts)
        case RamStmt.Until(_, rest) => collectRowVarRelSymStmt(rest)
        case RamStmt.Comment(_) => Nil
        case RamStmt.EstimateJoinSize(_, _, _, _) => Nil
    }

    ///
    /// Returns a list `(RowVar, RelSym)` in `op` in the order of nesting.
    ///
    @Internal
    pub def collectRowVarRelSymOp(op: RelOp): List[(RowVar, RelSym)] \ r = match op {
        case RelOp.Search(rv, relSym, rest) => (rv, relSym) :: collectRowVarRelSymOp(rest)
        case RelOp.Query(rv, relSym, _, _, rest) => (rv, relSym) :: collectRowVarRelSymOp(rest)
        case RelOp.Functional(_, _, _, rest, _) => collectRowVarRelSymOp(rest)
        case RelOp.Project(_, _) => Nil
        case RelOp.If(_, rest) => collectRowVarRelSymOp(rest)
    }

    ///
    /// Returns a list `(RowVar, arity)` in `program` in the order of the nesting.
    ///
    @Internal
    pub def collectRowVarArity(program: RamProgram): List[(RowVar, Int32)] = 
        collectRowVarRelSym(program) |> List.map(match (rv, RelSym.Symbol(_, arity, _)) -> (rv, arity))

}
