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
    use Fixpoint.Ast.Ram.{PredicateState, RelSym, Search, IndexInformation}
    use Fixpoint.Ast.Shared.PredSym
    use Fixpoint.SubstitutePredSym

    /////////////////////////////////////////////////////////////////////////////
    // RamStmt                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    // TODO: Add 'exit' at some point, when stuff starts to work.

    @Internal
    pub enum RamStmt {
        case Insert(RelOp)
        // Boxed -> Boxed -> Boxed and IntToBox here only means something for lattice-tuples.
        case Merge(Int32, Int32, Boxed -> Boxed -> Boxed, IntToBox)
        case Swap(Int32, Int32)
        case Purge(Int32)
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
                case RamStmt.Merge(src, dst, _, _) => "merge ${src} into ${dst}"
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
        // (RowVar, searchIndex, writeTuple, body)
        case Search(Int32, Int32, Vector[WriteTuple], RelOp)
        // (RowVar, searchIndex, meetWith, meet, writeTuple, body)
        case SearchLattice(Int32, Int32, Int32, Boxed -> Boxed -> Boxed, Vector[WriteTuple], RelOp)
        // (RowVar: EnvPos, searchIndex, body)
        case Query(Int32, Int32, Vector[WriteTuple], RelOp)
        // (RowVar: EnvPos, searchIndex, meetWith, meet, writeLatticeTo, body)
        case QueryLattice(Int32, Int32, Int32, Boxed -> Boxed -> Boxed, Vector[WriteTuple], RelOp)
        // The first is from the second is to.
        case Functional(Int32, Vector[Boxed] -> Vector[Vector[Boxed]], Vector[RamTerm], Vector[WriteTuple], RelOp, Vector[IntToBox], Vector[IntToBox])
        // The Boxed is Bot. The first Boxed -> Boxed -> Boxed is leq and the second is lub.
        case Project(Vector[RamTerm], Int32, Boxed, Boxed -> Boxed -> Bool, Boxed -> Boxed -> Boxed, IntToBox)
        case If(Vector[BoolExp], RelOp)
    }

    instance ToString[RelOp] {
        pub def toString(op: RelOp): String =
            let nl = String.lineSeparator();
            match op {
                case RelOp.Search(var, relSym, _, body) =>
                    "search ${var} ∈ ${relSym} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Query(var, ramSym, prefixQuery, body) =>
                    let qry = Vector.joinWith(match term -> {
                        ToString.toString(term)
                    }, " ∧ ", prefixQuery);
                    "Query {${var} ∈ ${ramSym} | ${qry}} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.SearchLattice(var, relSym, _, _, _, body) =>
                    "search ${var} ∈ ${relSym} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.QueryLattice(var, ramSym, _, _, prefixQuery, body) =>
                    let qry = Vector.joinWith(match term -> {
                        ToString.toString(term)
                    }, " ∧ ", prefixQuery);
                    "Query {${var} ∈ ${ramSym} | ${qry}} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Functional(id, _, terms, _, body, _, _) => // TODO: Get correct id?
                    "loop(${id} <- f(${terms |> Vector.join(", ")})) do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Project(terms, ramSym, _, _, _, _) =>
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
        case IsEmpty(Int32)
        // Boxed -> Boxed -> bool is leq.
        case NotMemberOf(Vector[RamTerm], Int32, Boxed -> Boxed -> Bool, IntToBox)
        case Eq(RamTerm, RamTerm)
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
                case BoolExp.NotMemberOf(terms, ramSym, _, _) => "(${terms |> Vector.join(", ")}) not in ${ramSym}"
                case BoolExp.Eq(lhs, rhs) => "${lhs} == ${rhs}"
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
        case Lit(Int64, Boxed)
        // case LoadIndex(IndexInMemory)
        case LoadFromTuple(Int32, Int32, IntToBox)
        case LoadLatVar(Int32)
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
            case RamTerm.Lit(v, _) => "%{v}"
            case RamTerm.LoadFromTuple(tupleIndex, indexInTuple, _) => "$LoadT[${tupleIndex}][${indexInTuple}]"
            case RamTerm.LoadLatVar(i) => "$LoadLatVar[${i}]"
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
        case Program(RamStmt, Facts, PredicateState, IndexInformation, Arities)
    }

    type alias Arities = Vector[Int32]

    type alias Tuple[r: Eff] = Array[Int64, r]

    // (a, b, c) meaning: Write number a from the read values to search environment number b at position c.
    // Aka (searchEnv[b])[c] = read[a]
    pub type alias WriteTuple = (Int32, Int32, Int32)

    pub type alias Facts = Map[RelSym, Vector[(Vector[Int64], Boxed)]]
}
