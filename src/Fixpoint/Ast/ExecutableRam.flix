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

mod Fixpoint.Ast.ExecutableRam {
    use Fixpoint.Boxed;
    use PredTrack.PredSymMapInternal
    use Fixpoint.Ast.ExecutableRam.RamStmt
    use Fixpoint.Ast.ExecutableRam.Facts
    use Fixpoint.Ast.Ram.Search
    use Fixpoint.Ast.Ram.{PredicateState, RelSym, Search, IndexInformation}


    use Fixpoint.Ast.Shared.Denotation
    use Fixpoint.Ast.Shared.PredSym
    use Fixpoint.PredSymsOf
    use Fixpoint.SubstitutePredSym
    use Fixpoint.Ast.Ram.RelSym

    /////////////////////////////////////////////////////////////////////////////
    // RamStmt                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    // TODO: Add 'exit' at some point, when stuff starts to work.

    @Internal
    pub enum RamStmt {
        case Insert(RelOp)
        // case Merge(Index, Index, IntToBox) // IntToBox here only means something for lattice-tuples.
        // case Swap(Index, Index)
        // case Purge(Index)
        case Merge(RelSym, RelSym, IntToBox) // IntToBox here only means something for lattice-tuples.
        case Swap(RelSym, RelSym)
        case Purge(RelSym)
        case Seq(Vector[RamStmt])
        case Par(Vector[RamStmt])
        case Until(Vector[BoolExp], RamStmt)
        case Comment(String)
    }

    instance ToString[RamStmt] {
        pub def toString(stmt: RamStmt): String =
            let nl = String.lineSeparator();
            match stmt {
                case RamStmt.Insert(op) => ToString.toString(op)
                case RamStmt.Merge(src, dst, _) => "merge ${src} into ${dst}"
                case RamStmt.Swap(lhs, rhs) => "Swap ${lhs} and ${rhs}"
                case RamStmt.Purge(ramSym) => "purge ${ramSym}"
                case RamStmt.Seq(xs) => Vector.join(";${nl}", xs)
                case RamStmt.Until(test, body) =>
                    let tst = test |> Vector.join(" && ");
                    "until(${tst}) do${nl}${String.indent(4, "${body}")}end"
                case RamStmt.Comment(comment) => "// ${comment}"
                case RamStmt.Par(xs) => Vector.join("|${nl}", xs)
            }
    }

    /////////////////////////////////////////////////////////////////////////////
    // RelOp                                                                   //
    /////////////////////////////////////////////////////////////////////////////
    
    @Internal
    pub enum RelOp {
        case Search(Int32, RelSym, (Vector[WriteTuple], Vector[WriteTuple]), RelOp) // Loop through RelSym, saving values in TupleVar with body of loop RelOp.
        case SearchWithIndex(Int32, RelSym, Vector[BoolExp], Int32, RelOp)
        case Functional(Int32, Vector[Boxed] -> Vector[Vector[Boxed]], Vector[RamTerm], RelOp, Vector[IntToBox], Vector[IntToBox]) // The first is from the second is to.
        case Project(Vector[RamTerm], RelSym, IntToBox)
        case If(Vector[BoolExp], RelOp)
    }

    instance ToString[RelOp] {
        pub def toString(op: RelOp): String =
            let nl = String.lineSeparator();
            match op {
                case RelOp.Search(var, ramSym, _, body) =>
                    "search ${var} ∈ ${ramSym} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.SearchWithIndex(var, ramSym, prefixQuery, _, body) =>
                    let qry = Vector.joinWith(match term -> {
                        ToString.toString(term)
                    }, " ∧ ", prefixQuery);
                    "SearchWithIndex {${var} ∈ ${ramSym} | ${qry}} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Functional(id, _, terms, body, _, _) => // TODO: Get correct id?
                    "loop(${id} <- f(${terms |> Vector.join(", ")})) do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Project(terms, ramSym, _) =>
                    "project (${terms |> Vector.join(", ")}) into ${ramSym}"
                case RelOp.If(test, then) =>
                    let tst = test |> Vector.join(" ∧ ");
                    "if(${tst}) then${nl}${String.indent(4, "${then}")}end"
            }
    }

    /////////////////////////////////////////////////////////////////////////////
    // BoolExp                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    /**
    TODO: Maybe add not equal? Could allow more optimal searching of structures
    */

    @Internal
    pub enum BoolExp {
        case IsEmpty(RelSym)
        case NotMemberOf(Vector[RamTerm], RelSym, IntToBox)
        case Eq(RamTerm, RamTerm)
        case Leq(Boxed -> Boxed  -> Bool, RamTerm, RamTerm, IntToBox)
        case Guard0(Unit -> Bool)
        case Guard1(Boxed -> Bool, RamTerm, IntToBox)
        case Guard2(Boxed -> Boxed  -> Bool, RamTerm, RamTerm, IntToBox, IntToBox)
        case Guard3(Boxed -> Boxed  -> Boxed -> Bool, RamTerm, RamTerm, RamTerm, IntToBox, IntToBox, IntToBox)
        case Guard4(Boxed -> Boxed  -> Boxed -> Boxed -> Bool, RamTerm, RamTerm, RamTerm, RamTerm, IntToBox, IntToBox, IntToBox, IntToBox)
        case Guard5(Boxed -> Boxed  -> Boxed -> Boxed -> Boxed -> Bool, RamTerm, RamTerm, RamTerm, RamTerm, RamTerm, IntToBox, IntToBox, IntToBox, IntToBox, IntToBox)
    }

    instance ToString[BoolExp] {
        pub def toString(exp: BoolExp): String =
            match exp {
                case BoolExp.IsEmpty(ramSym) => "${ramSym} == {}"
                case BoolExp.NotMemberOf(terms, ramSym, _) => "(${terms |> Vector.join(", ")}) not in ${ramSym}"
                case BoolExp.Eq(lhs, rhs) => "${lhs} == ${rhs}"
                case BoolExp.Leq(_, lhs, rhs, _) => "${lhs} <= ${rhs}"
                case BoolExp.Guard0(_) => "<clo>()"
                case BoolExp.Guard1(_, v, _) => "<clo>(${v})"
                case BoolExp.Guard2(_, v1, v2, _, _) => "<clo>(${v1}, ${v2})"
                case BoolExp.Guard3(_, v1, v2, v3, _, _ ,_) => "<clo>(${v1}, ${v2}, ${v3})"
                case BoolExp.Guard4(_, v1, v2, v3, v4, _, _ ,_, _) => "<clo>(${v1}, ${v2}, ${v3}, ${v4})"
                case BoolExp.Guard5(_, v1, v2, v3, v4, v5, _, _ ,_, _, _) => "<clo>(${v1}, ${v2}, ${v3}, ${v4}, ${v5})"
            }
    }

    /////////////////////////////////////////////////////////////////////////////
    // RamTerm                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    ///
    /// Represents a RAM term.
    ///
    /// `RowLoad(x, i)` represents an index into the tuple
    /// bound to the local variable `x`, i.e. `x[i]`.
    ///
    /// `LoadLatVar(x)` represents the lattice component in the tuple
    /// bound to the local variable `x`.
    ///
    @Internal
    pub enum RamTerm {
        case Lit(Int64)
        case LoadIndex(IndexInMemory)
        case Meet(Boxed -> Boxed  -> Boxed, RamTerm, RamTerm, IntToBox)
        // The first indices are the input. The last is the output
        case App0(Unit -> Boxed, IntToBox)
        case App1(Boxed -> Boxed, RamTerm, IntToBox, IntToBox)
        case App2(Boxed -> Boxed  -> Boxed, RamTerm, RamTerm, IntToBox, IntToBox, IntToBox)
        case App3(Boxed -> Boxed  -> Boxed -> Boxed, RamTerm, RamTerm, RamTerm, IntToBox, IntToBox, IntToBox, IntToBox)
        case App4(Boxed -> Boxed  -> Boxed -> Boxed -> Boxed, RamTerm, RamTerm, RamTerm, RamTerm, IntToBox, IntToBox, IntToBox, IntToBox, IntToBox)
        case App5(Boxed -> Boxed  -> Boxed -> Boxed -> Boxed -> Boxed, RamTerm, RamTerm, RamTerm, RamTerm, RamTerm, IntToBox, IntToBox, IntToBox, IntToBox, IntToBox, IntToBox)
    }

    instance ToString[RamTerm] {
        pub def toString(term: RamTerm): String = match term {
            case RamTerm.Lit(v) => "%{v}"
            case RamTerm.LoadIndex(index) => "$Load[${index}]"
            case RamTerm.Meet(_, lhs, rhs, _) => "(${lhs} ⊓ ${rhs})"
            case RamTerm.App0(_, _) => "<clo>()"
            case RamTerm.App1(_, v, _, _) => "<clo>(${v})"
            case RamTerm.App2(_, v1, v2, _, _, _) => "<clo>(${v1}, ${v2})"
            case RamTerm.App3(_, v1, v2, v3, _, _, _, _) => "<clo>(${v1}, ${v2}, ${v3})"
            case RamTerm.App4(_, v1, v2, v3, v4, _, _, _, _, _) => "<clo>(${v1}, ${v2}, ${v3}, ${v4})"
            case RamTerm.App5(_, v1, v2, v3, v4, v5, _, _, _, _, _, _) => "<clo>(${v1}, ${v2}, ${v3}, ${v4}, ${v5})"
        }
    }

    /////////////////////////////////////////////////////////////////////////////
    // RelSym                                                                  //
    /////////////////////////////////////////////////////////////////////////////

    pub type alias RelSym = RelSym

    type alias IndexInMemory = Int32
    type alias IntToBox = Int32


    // RamProgram consisting of the the ExecutableRam program/statements, the starting database/facts and information about which indices should be used.
    pub enum RamProgram {
        case Program(RamStmt, Facts, PredicateState, IndexInformation)
    }

    type alias Tuple[r: Eff] = Array[Int64, r]

    type alias WriteTuple = (Int32, Int32, Int32)

    pub type alias Facts = Map[RelSym, Vector[Vector[Int64]]]
}
