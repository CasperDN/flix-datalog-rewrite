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
    use Fixpoint.Boxed;
    use PredTrack.PredSymMapInternal
    // use Fixpoint.Ast.Ram.RamStmt
    // use Fixpoint.Ast.Ram.IndexInformation
    // use Fixpoint.Ast.Ram.Facts

    use Fixpoint.Ast.Shared.Denotation
    use Fixpoint.Ast.Shared.PredSym
    use Fixpoint.PredSymsOf
    use Fixpoint.SubstitutePredSym

    /////////////////////////////////////////////////////////////////////////////
    // RamStmt                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    // TODO: Add 'exit' at some point, when stuff starts to work.

    @Internal
    pub enum RamStmt {
        case Insert(RelOp)
        case Merge(RelSym, RelSym)
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
    pub enum RelOp {
        case Search(TupleVar, RelSym, RelOp) // Loop through RelSym, saving values in TupleVar with body of loop RelOp.
        // case Query(TupleVar, RelSym, Vector[(Int32, TupleVar)], RelOp) // Loop through RelSym saving values in TupleVar 

        // TODO: Add extra field describing which index to use. Could use a simple int32.
        case SearchWithIndex(TupleVar, RelSym, Vector[BoolExp], Int32, RelOp)
        // case SearchWithIndex(TupleVar, RelSym, Vector[QueryExp], RelOp)
        case Functional(TupleVar, Vector[Boxed] -> Vector[Vector[Boxed]], Vector[RamTerm], RelOp, Int32) // The last is the arity
        case Project(Vector[RamTerm], RelSym)
        case If(Vector[BoolExp], RelOp)
    }

    instance ToString[RelOp] {
        pub def toString(op: RelOp): String =
            let nl = String.lineSeparator();
            match op {
                case RelOp.Search(var, ramSym, body) =>
                    "search ${var} ∈ ${ramSym} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.SearchWithIndex(var, ramSym, prefixQuery, _, body) =>
                    let qry = Vector.joinWith(match term -> {
                        ToString.toString(term)
                    }, " ∧ ", prefixQuery);
                    "SearchWithIndex {${var} ∈ ${ramSym} | ${qry}} do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Functional(TupleVar.Named(id), _, terms, body, _) => // TODO: Get correct id?
                    "loop(${id} <- f(${terms |> Vector.join(", ")})) do${nl}${String.indent(4, "${body}")}end"
                case RelOp.Project(terms, ramSym) =>
                    "project (${terms |> Vector.join(", ")}) into ${ramSym}"
                case RelOp.If(test, then) =>
                    let tst = test |> Vector.join(" ∧ ");
                    "if(${tst}) then${nl}${String.indent(4, "${then}")}end"
            }
    }

    /////////////////////////////////////////////////////////////////////////////
    // BoolExp                                                                 //
    /////////////////////////////////////////////////////////////////////////////

    @Internal
    pub enum BoolExp {
        case IsEmpty(RelSym)
        case NotMemberOf(Vector[RamTerm], RelSym)
        case Eq(RamTerm, RamTerm)
        case Leq(Boxed -> Boxed  -> Bool, RamTerm, RamTerm)
        case Guard0(Unit -> Bool)
        case Guard1(Boxed ->Bool, RamTerm)
        case Guard2(Boxed -> Boxed  -> Bool, RamTerm, RamTerm)
        case Guard3(Boxed -> Boxed  -> Boxed -> Bool, RamTerm, RamTerm, RamTerm)
        case Guard4(Boxed -> Boxed  -> Boxed -> Boxed -> Bool, RamTerm, RamTerm, RamTerm, RamTerm)
        case Guard5(Boxed -> Boxed  -> Boxed -> Boxed -> Boxed -> Bool, RamTerm, RamTerm, RamTerm, RamTerm, RamTerm)
    }

    instance ToString[BoolExp] {
        pub def toString(exp: BoolExp): String =
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
    /// The RamId uniquely identifies the term
    @Internal
    pub enum RamTerm {
        case Lit(Boxed, RamId)
        case RowLoad(TupleVar, Int32, RelSym)
        case Meet(Boxed -> Boxed  -> Boxed, RamTerm, RamTerm, RamId)
        case App0(Unit -> Boxed, RamId)
        case App1(Boxed -> Boxed, RamTerm, RamId)
        case App2(Boxed -> Boxed  -> Boxed, RamTerm, RamTerm, RamId)
        case App3(Boxed -> Boxed  -> Boxed -> Boxed, RamTerm, RamTerm, RamTerm, RamId)
        case App4(Boxed -> Boxed  -> Boxed -> Boxed -> Boxed, RamTerm, RamTerm, RamTerm, RamTerm, RamId)
        case App5(Boxed -> Boxed  -> Boxed -> Boxed -> Boxed -> Boxed, RamTerm, RamTerm, RamTerm, RamTerm, RamTerm, RamId)
    }

    pub def getTermRamId(t: RamTerm): RamId = match t {
        case RamTerm.Lit(_, id) => id
        case RamTerm.RowLoad(TupleVar.Named(i), index, _) => RamId.TuplePos(i, index)
        case RamTerm.Meet(_, _, _, id) => id
        case RamTerm.App0(_, id) => id
        case RamTerm.App1(_ , _, id) => id
        case RamTerm.App2(_, _, _, id) => id
        case RamTerm.App3(_, _, _, _, id) => id
        case RamTerm.App4(_, _, _, _, _, id) => id
        case RamTerm.App5(_, _, _, _, _, _, id) => id
    }

    instance ToString[RamTerm] {
        pub def toString(term: RamTerm): String = match term {
            case RamTerm.Lit(v, _) => "%{v}"
            case RamTerm.RowLoad(var, index, _) => "${var}[${index}]"
            case RamTerm.Meet(_, lhs, rhs, _) => "(${lhs} ⊓ ${rhs})"
            case RamTerm.App0(_, _) => "<clo>()"
            case RamTerm.App1(_, v, _) => "<clo>(${v})"
            case RamTerm.App2(_, v1, v2, _) => "<clo>(${v1}, ${v2})"
            case RamTerm.App3(_, v1, v2, v3, _) => "<clo>(${v1}, ${v2}, ${v3})"
            case RamTerm.App4(_, v1, v2, v3, v4, _) => "<clo>(${v1}, ${v2}, ${v3}, ${v4})"
            case RamTerm.App5(_, v1, v2, v3, v4, v5, _) => "<clo>(${v1}, ${v2}, ${v3}, ${v4}, ${v5})"
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
    pub enum RelSym {
        case Symbol(PredSym, Int32, Denotation)
    }

    // TODO: Implement equality for PredSym using only int id.
    instance Eq[RelSym] {
        pub def eq(a: RelSym, b: RelSym): Bool = match (a, b) {
            case (RelSym.Symbol(s1, _, _),  RelSym.Symbol(s2, _, _))  => s1 == s2
        }
    }

    // TODO: Implement order for PredSym using only int id.
    instance Order[RelSym] {
        pub def compare(a: RelSym, b: RelSym): Comparison = match (a, b) {
            case (RelSym.Symbol(s1, _, _), RelSym.Symbol(s2, _, _)) =>  s1 <=> s2
        }
    }

    instance PredSymsOf[RelSym] {
        pub def predSymsOf(x: RelSym): Set[PredSym] = match x {
            case RelSym.Symbol(predSym, _, _)    => Set.singleton(predSym)
        }
    }

    instance SubstitutePredSym[RelSym] {
        pub def substitute(x: RelSym, s: Map[PredSym, PredSym]): RelSym = match x {
            case RelSym.Symbol(predSym, arity, den)  =>
                let newSym = Map.getWithDefault(predSym, predSym, s);
                RelSym.Symbol(newSym, arity, den)
        }
    }

    instance ToString[RelSym] {
        pub def toString(ramSym: RelSym): String = match ramSym {
            case RelSym.Symbol(sym, _, _)    => "${sym}"
        }
    }

    @Internal
    pub def toPredID(ramSym: RelSym): Int64 = match ramSym {
        case RelSym.Symbol(PredSym.PredSym(_, id), _, _) => id
    }

    @Internal
    pub def arityOf(ramSym: RelSym): Int32 = match ramSym {
        case RelSym.Symbol(_, arity, _) => arity
    }

    @Internal
    pub def toDenotation(ramSym: RelSym): Denotation = match ramSym {
        case RelSym.Symbol(_, _, den) => den
    }

    @Internal
    pub def toId(ramSym: RelSym): Int64 = match ramSym {
        case RelSym.Symbol(PredSym.PredSym(_, id), _, _) => id
    }

    @Internal
    pub def collectRelSym(program: RamProgram): List[RelSym] = region rc { match program {
        case RamProgram.Program(stmt, facts, _, _) =>
            let seen = MutSet.empty(rc);
            collectRelSymStmt(seen, stmt);
            Map.forEach(k -> _ -> MutSet.add(k, seen), facts);
            MutSet.toList(seen)
    }}

    @Internal
    pub def collectRelSymStmt(soFar: MutSet[RelSym, r], stmt: RamStmt): Unit \ r = match stmt {
        case RamStmt.Insert(op) => collectRelSymOp(soFar, op)
        case RamStmt.Merge(r1, r2) => MutSet.add(r1, soFar); MutSet.add(r2, soFar)
        case RamStmt.Swap(r1, r2) => MutSet.add(r1, soFar); MutSet.add(r2, soFar)
        case RamStmt.Purge(r1) => MutSet.add(r1, soFar)
        case RamStmt.Seq(stmts) => Vector.forEach(x -> collectRelSymStmt(soFar, x), stmts)
        case RamStmt.Par(stmts) => Vector.forEach(x -> collectRelSymStmt(soFar, x), stmts)
        case RamStmt.Until(bools, rest) => collectRelSymStmt(soFar, rest); Vector.forEach(collectRelSymBool(soFar), bools)
        case RamStmt.Comment(_) => ()
    }

    def collectRelSymOp(soFar: MutSet[RelSym, r], op: RelOp): Unit \ r = match op {
        case RelOp.Search(_, r1, rest) => MutSet.add(r1, soFar); collectRelSymOp(soFar, rest)
        case RelOp.SearchWithIndex(_, r1, bools, _, rest) => MutSet.add(r1, soFar); collectRelSymOp(soFar, rest); Vector.forEach(collectRelSymBool(soFar), bools)
        case RelOp.Functional(_, _, terms, rest, _) => collectRelSymOp(soFar, rest); Vector.forEach(collectRelSymTerm(soFar), terms)
        case RelOp.Project(terms, r1) => MutSet.add(r1, soFar); Vector.forEach(collectRelSymTerm(soFar), terms)
        case RelOp.If(bools, rest) => Vector.forEach(collectRelSymBool(soFar), bools); collectRelSymOp(soFar, rest)
    }

    def collectRelSymBool(soFar: MutSet[RelSym, r], bool: BoolExp): Unit \ r = match bool {
        case BoolExp.IsEmpty(r1) => MutSet.add(r1, soFar)
        case BoolExp.NotMemberOf(terms, r1) => MutSet.add(r1, soFar); Vector.forEach(collectRelSymTerm(soFar), terms)
        case BoolExp.Eq(t1, t2) => collectRelSymTerm(soFar, t1); collectRelSymTerm(soFar, t2)
        case BoolExp.Leq(_, t1, t2) => collectRelSymTerm(soFar, t1); collectRelSymTerm(soFar, t2)
        case BoolExp.Guard0(_) => ()
        case BoolExp.Guard1(_, t1) => collectRelSymTerm(soFar, t1)
        case BoolExp.Guard2(_, t1, t2) => collectRelSymTerm(soFar, t1); collectRelSymTerm(soFar, t2)
        case BoolExp.Guard3(_, t1, t2, t3) => collectRelSymTerm(soFar, t1); collectRelSymTerm(soFar, t2); collectRelSymTerm(soFar, t3)
        case BoolExp.Guard4(_, t1, t2, t3, t4) => collectRelSymTerm(soFar, t1); collectRelSymTerm(soFar, t2); collectRelSymTerm(soFar, t3); collectRelSymTerm(soFar, t4)
        case BoolExp.Guard5(_, t1, t2, t3, t4, t5) => collectRelSymTerm(soFar, t1); collectRelSymTerm(soFar, t2); collectRelSymTerm(soFar, t3); collectRelSymTerm(soFar, t4); collectRelSymTerm(soFar, t5)
    }

    def collectRelSymTerm(soFar: MutSet[RelSym, r], term: RamTerm): Unit \ r = match term {
        case RamTerm.Lit(_, _) => ()
        case RamTerm.RowLoad(_, _, r1) => MutSet.add(r1, soFar)
        case RamTerm.Meet(_, _, _, _) => ()
        case RamTerm.App0(_, _) => ()
        case RamTerm.App1(_, _, _) => ()
        case RamTerm.App2(_, _, _, _) => ()
        case RamTerm.App3(_, _, _, _, _) => ()
        case RamTerm.App4(_, _, _, _, _, _) => ()
        case RamTerm.App5(_, _, _, _, _, _, _) => ()
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

    // A RamId is is either an identifier on a RAM-instruction, or an index in a RelSym.
    // Identifiers should be <0 for RamId.Id. Might be avoidable
    pub enum RamId {
        case Id(Int32) // (ID)
        // case InID(Int32, Int32) // (ID, index)
        case InID(Int32, Int32) // (OutID, index)
        case TuplePos(Int32, Int32) // (TupleVar, index)
        case RelPos(Int64, Int32) // (PredSym, index). This does not exist in the RAM, but is useful for normalization.
    }

    instance Eq[RamId] {
        pub def eq(a: RamId, b: RamId): Bool = match (a, b) {
            case (RamId.Id(i1), RamId.Id(i2)) => i1 == i2
            // case (RamId.InID(id1, index1), RamId.InID(id2, index2)) => id1 == id2 and index1 == index2
            case (RamId.InID(id1, index1), RamId.InID(id2, index2)) => id1 == id2 and index1 == index2
            case (RamId.TuplePos(i0, i1), RamId.TuplePos(j0, j1)) => i0 == j0 and i1 == j1
            case (RamId.RelPos(i0, i1), RamId.RelPos(j0, j1)) => i0 == j0 and i1 == j1
        //    case (TupleVar.Index(i1), TupleVar.Index(i2)) => i1 <=> i2
            case _ => false
        }
    }

    instance Order[RamId] {
        pub def compare(a: RamId, b: RamId): Comparison = match (a, b) {
            case (RamId.Id(i1), RamId.Id(i2)) => i1 <=> i2
            // case (RamId.)
            case (RamId.TuplePos(i0, i1), RamId.TuplePos(j0, j1)) =>
                let firstComp = i0 <=> j0;
                if (firstComp != Comparison.EqualTo) firstComp else i1 <=> j1
            case (RamId.RelPos(i0, i1), RamId.RelPos(j0, j1)) =>
                let firstComp = i0 <=> j0;
                if (firstComp != Comparison.EqualTo) firstComp else i1 <=> j1
            case (RamId.InID(i0, i1), RamId.InID(j0, j1)) =>
                let firstComp = i0 <=> j0;
                if (firstComp != Comparison.EqualTo) firstComp else i1 <=> j1
            // case (RamId.InID(i0, i1), RamId.InID(j0, j1)) =>
            //     let firstComp = i0 <=> j0;
            //     if (firstComp != Comparison.EqualTo) firstComp else i1 <=> j1
            // TODO: This is perhaps not transitive. Should add cases for all...
            case (RamId.TuplePos(_, _), _) => Comparison.LessThan
            case (_,  RamId.TuplePos(_, _)) => Comparison.GreaterThan
            case (RamId.RelPos(_, _), _) => Comparison.LessThan
            case (_, RamId.RelPos(_, _)) => Comparison.GreaterThan
            case (RamId.Id(_), _) => Comparison.LessThan
            case (_, RamId.Id(_)) => Comparison.GreaterThan
            case (RamId.InID(_, _), _) => Comparison.LessThan
            case (_, RamId.InID(_, _)) => Comparison.GreaterThan


            // case (RamId.Id(_), _) => Comparison.LessThan
            // case (RamId.InID(_, _), _) => Comparison.GreaterThan
            // case _ => ???
        }
    }

    // RamProgram consisting of the the Ram program/statements, the starting database/facts and information about which indices should be used.
    pub enum RamProgram {
        case Program(RamStmt, Facts, PredicateState, IndexInformation)
    }

    pub type alias PredicateState = PredTrack.PredSymMapInternal

    pub type alias Facts = Map[RelSym, Vector[Vector[Boxed]]]

    pub type alias Search = Vector[Int32]

    
    pub type alias ConstructedIndexes = Map[RelSym, Vector[Search]]

    //The first is a list of the indices that should be made. The second is a map describing where they are suppoesed to be saved at runtime.
    pub type alias IndexInformation = (ConstructedIndexes, Map[(RelSym, Int32), Int32])


}
