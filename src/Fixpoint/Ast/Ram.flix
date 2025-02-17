   use IoError.ErrorKind
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

mod Fixpoint.Ast.Ram {
    use Fixpoint.Ast.Ram.IndexInformation
    use Fixpoint.Ast.Ram.FactInformation

    use Fixpoint.Ast.Shared.Denotation
    use Fixpoint.Ast.Shared.PredSym
    use Fixpoint.PredSymsOf
    use Fixpoint.SubstitutePredSym

    /////////////////////////////////////////////////////////////////////////////
    // RamStmt                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    // TODO: Add 'exit' at some point, when stuff starts to work.

    @Internal
    pub enum RamStmt[v] {
        case Insert(RelOp[v])
        case Merge(RelSym[v], RelSym[v])
        case Swap(RelSym[v], RelSym[v])
        case Purge(RelSym[v])
        case Seq(Vector[RamStmt[v]])
        case Par(Vector[RamStmt[v]])
        case Until(Vector[BoolExp[v]], RamStmt[v])
        case Comment(String)
    }

    instance ToString[RamStmt[v]] {
        pub def toString(stmt: RamStmt[v]): String =
            let nl = String.lineSeparator();
            match stmt {
                case RamStmt.Insert(op) => ToString.toString(op)
                case RamStmt.Merge(src, dst) => "merge ${src} into ${dst}"
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
    pub enum RelOp[v] {
        case Search(TupleVar, RelSym[v], RelOp[v]) // Loop through RelSym, saving values in TupleVar with body of loop RelOp[v].
        // case Query(TupleVar, RelSym[v], Vector[(Int32, TupleVar[v])], RelOp[v]) // Loop through RelSym saving values in TupleVar 

        // TODO: Add extra field describing which index to use. Could use a simple int32.
        case SearchWithIndex(TupleVar, RelSym[v], Vector[QueryExp[v]], RelOp[v])
        case Functional(TupleVar, Vector[v] -> Vector[Vector[v]], Vector[RamTerm[v]], RelOp[v])
        case Project(Vector[RamTerm[v]], RelSym[v])
        case If(Vector[BoolExp[v]], RelOp[v])
    }

    instance ToString[RelOp[v]] {
        pub def toString(op: RelOp[v]): String =
            let nl = String.lineSeparator();
            match op {
                case RelOp.Search(var, ramSym, body) =>
                    "search ${var} ∈ ${ramSym} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.SearchWithIndex(var, ramSym, prefixQuery, body) =>
                    let qry = Vector.joinWith(match term -> {
                        ToString.toString(term)
                    }, " ∧ ", prefixQuery);
                    "SearchWithIndex {${var} ∈ ${ramSym} | ${qry}} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Functional(TupleVar.Named(id), _, terms, body) => // TODO: Get correct id?
                    "loop(${id} <- f(${terms |> Vector.join(", ")})) do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Project(terms, ramSym) =>
                    "project (${terms |> Vector.join(", ")}) into ${ramSym}"
                case RelOp.If(test, then) =>
                    let tst = test |> Vector.join(" ∧ ");
                    "if(${tst}) then${nl}${String.indent(4, "${then}")}end"
            }
    }

    /////////////////////////////////////////////////////////////////////////////
    // QueryExp                                                                //
    /////////////////////////////////////////////////////////////////////////////

    // TODO: Possibly add support for more searches.
    // TODO: Decide whether to merge this with BoolExp, and then just let the interpreter do if else after, if it cannot make the data structure handle it?
    @Internal
    pub enum QueryExp[v] {
        case Eq(RamTerm[v], RamTerm[v])
        case Neq(RamTerm[v], RamTerm[v])
        // case MemberOf(Vector[RamTerm[v]], RelSym[v])
    }

    instance ToString[QueryExp[v]] {
        pub def toString(exp: QueryExp[v]): String =
            match exp {
                case QueryExp.Eq(i1, i2) => "${i1} = ${i2}"
                case QueryExp.Neq(i1, i2) => "${i1} ≠ ${i2}"
            }
    }


    /////////////////////////////////////////////////////////////////////////////
    // BoolExp                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    /**
    TODO: Maybe add not equal? Could allow more optimal searching of structures
    */

    @Internal
    pub enum BoolExp[v] {
        case IsEmpty(RelSym[v])
        case NotMemberOf(Vector[RamTerm[v]], RelSym[v])
        case Eq(RamTerm[v], RamTerm[v])
        case Leq(v -> v -> Bool, RamTerm[v], RamTerm[v])
        case Guard0(Unit -> Bool)
        case Guard1(v -> Bool, RamTerm[v])
        case Guard2(v -> v -> Bool, RamTerm[v], RamTerm[v])
        case Guard3(v -> v -> v -> Bool, RamTerm[v], RamTerm[v], RamTerm[v])
        case Guard4(v -> v -> v -> v -> Bool, RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v])
        case Guard5(v -> v -> v -> v -> v -> Bool, RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v])
    }

    instance ToString[BoolExp[v]] {
        pub def toString(exp: BoolExp[v]): String =
            match exp {
                case BoolExp.IsEmpty(ramSym) => "${ramSym} == {}"
                case BoolExp.NotMemberOf(terms, ramSym) => "(${terms |> Vector.join(", ")}) not in ${ramSym}"
                case BoolExp.Eq(lhs, rhs) => "${lhs} == ${rhs}"
                case BoolExp.Leq(_, lhs, rhs) => "${lhs} <= ${rhs}"
                case BoolExp.Guard0(_) => "<clo>()"
                case BoolExp.Guard1(_, v) => "<clo>(${v})"
                case BoolExp.Guard2(_, v1, v2) => "<clo>(${v1}, ${v2})"
                case BoolExp.Guard3(_, v1, v2, v3) => "<clo>(${v1}, ${v2}, ${v3})"
                case BoolExp.Guard4(_, v1, v2, v3, v4) => "<clo>(${v1}, ${v2}, ${v3}, ${v4})"
                case BoolExp.Guard5(_, v1, v2, v3, v4, v5) => "<clo>(${v1}, ${v2}, ${v3}, ${v4}, ${v5})"
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
    pub enum RamTerm[v] {
        case Lit(v)
        case RowLoad(TupleVar, Int32)
        case LoadLatVar(TupleVar)
        case Meet(v -> v -> v, RamTerm[v], RamTerm[v])
        case App0(Unit -> v)
        case App1(v -> v, RamTerm[v])
        case App2(v -> v -> v, RamTerm[v], RamTerm[v])
        case App3(v -> v -> v -> v, RamTerm[v], RamTerm[v], RamTerm[v])
        case App4(v -> v -> v -> v -> v, RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v])
        case App5(v -> v -> v -> v -> v -> v, RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v], RamTerm[v])
    }

    instance ToString[RamTerm[v]] {
        pub def toString(term: RamTerm[v]): String = match term {
            case RamTerm.Lit(v) => "%{v}"
            case RamTerm.RowLoad(var, index) => "${var}[${index}]"
            case RamTerm.LoadLatVar(var) => "${var}[-1]"
            case RamTerm.Meet(_, lhs, rhs) => "(${lhs} ⊓ ${rhs})"
            case RamTerm.App0(_) => "<clo>()"
            case RamTerm.App1(_, v) => "<clo>(${v})"
            case RamTerm.App2(_, v1, v2) => "<clo>(${v1}, ${v2})"
            case RamTerm.App3(_, v1, v2, v3) => "<clo>(${v1}, ${v2}, ${v3})"
            case RamTerm.App4(_, v1, v2, v3, v4) => "<clo>(${v1}, ${v2}, ${v3}, ${v4})"
            case RamTerm.App5(_, v1, v2, v3, v4, v5) => "<clo>(${v1}, ${v2}, ${v3}, ${v4}, ${v5})"
        }
    }

    /////////////////////////////////////////////////////////////////////////////
    // RelSym                                                                  //
    /////////////////////////////////////////////////////////////////////////////

    /**
        Represents the relations (also delta relations) of the program.
            The first is the symbol of the relation
            The second parameter is the arity
            The third depends denotes whether we are dealing with a lattice or a 'normal' relation.
    */

    @Internal
    pub enum RelSym[v] {
        case Symbol(PredSym, Int32, Denotation[v])
    }

    // TODO: Implement equality for PredSym using only int id.
    instance Eq[RelSym[v]] {
        pub def eq(a: RelSym[v], b: RelSym[v]): Bool = match (a, b) {
            case (RelSym.Symbol(s1, _, _),  RelSym.Symbol(s2, _, _))  => s1 == s2
        }
    }

    // TODO: Implement order for PredSym using only int id.
    instance Order[RelSym[v]] {
        pub def compare(a: RelSym[v], b: RelSym[v]): Comparison = match (a, b) {
            case (RelSym.Symbol(s1, _, _), RelSym.Symbol(s2, _, _)) =>  s1 <=> s2
        }
    }

    instance PredSymsOf[RelSym[v]] {
        pub def predSymsOf(x: RelSym[v]): Set[PredSym] = match x {
            case RelSym.Symbol(predSym, _, _)    => Set.singleton(predSym)
        }
    }

    instance SubstitutePredSym[RelSym[v]] {
        pub def substitute(x: RelSym[v], s: Map[PredSym, PredSym]): RelSym[v] = match x {
            case RelSym.Symbol(predSym, arity, den)  =>
                let newSym = Map.getWithDefault(predSym, predSym, s);
                RelSym.Symbol(newSym, arity, den)
        }
    }

    instance ToString[RelSym[v]] {
        pub def toString(ramSym: RelSym[v]): String = match ramSym {
            case RelSym.Symbol(sym, _, _)    => "${sym}"
        }
    }

    @Internal
    pub def arityOf(ramSym: RelSym[v]): Int32 = match ramSym {
        case RelSym.Symbol(_, arity, _) => arity
    }

    @Internal
    pub def toDenotation(ramSym: RelSym[v]): Denotation[v] = match ramSym {
        case RelSym.Symbol(_, _, den) => den
    }

    /////////////////////////////////////////////////////////////////////////////
    // TupleVar                                                                //
    /////////////////////////////////////////////////////////////////////////////

    /**
    Note that the id is supposed to be unique

    For code:
        search e1 ∈ Edge  do 
            search e2 ∈ Edge do
                ...

    'e1' and 'e2' would be the TupleVars.
    */

    @Internal
    pub enum TupleVar with Eq {
        case Named(Int32)
        //case Index(Int32)
    }

    instance ToString[TupleVar] {
        pub def toString(var: TupleVar): String = match var {
            case TupleVar.Named(id) => "x${id}$"
        //    case TupleVar.Index(i) => "${i}$"
        }
    }

    instance Order[TupleVar] {
        pub def compare(a: TupleVar, b: TupleVar): Comparison = match (a, b) {
            case (TupleVar.Named(i1), TupleVar.Named(i2)) => i1 <=> i2
        //    case (TupleVar.Index(i1), TupleVar.Index(i2)) => i1 <=> i2
            case _ => ?bug
        }
    }


    // RamProgram consisting of the the Ram program/statements, the starting database/facts and information about which indices should be used.
    pub enum RamProgram[v] {
        case Program(RamStmt[v], FactInformation[v], MetaInformation[v], IndexInformation[v])
    }

    pub type alias MetaInformation[v] = PredTrack.PredSymMapInternal[v]

    pub type alias FactInformation[v] = Map[Int64, Vector[Vector[v]]]
    // TODO: Implement this
    pub type alias IndexInformation[v] = Int32
}
