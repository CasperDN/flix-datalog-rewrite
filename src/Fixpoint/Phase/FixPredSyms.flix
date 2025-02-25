/**
Purpose of file:
Apparently the rest of the Flix compiler does not use the int part of PredSym's at all
Therefore remap all PredSym's such the int part can be used as an identifier, instead of the string.
Also: Why does it even have it, if it is not used and why use strings internally as identifiers?
*/

mod Fixpoint.Phase.FixPredSyms {
    use Fixpoint.Phase.FixPredSyms.FixInformation

    use Fixpoint.Ast.Ram.{RamStmt, RelOp, RelSym, RamTerm, BoolExp, TupleVar, FactInformation, MetaInformation, RamProgram}
    use Fixpoint.Ast.Datalog.{Datalog, Constraint, BodyPredicate, BodyTerm, HeadTerm, Polarity, VarSym}
    use Fixpoint.Ast.Datalog.Datalog.{Datalog, Model}
    use Fixpoint.Ast.Datalog.Constraint.Constraint
    use Fixpoint.Ast.Datalog.HeadPredicate
    use Fixpoint.Ast.Datalog.HeadPredicate.HeadAtom
    use Fixpoint.Ast.Datalog.BodyPredicate.{BodyAtom}
    use Fixpoint.Ast.Datalog.BodyPredicate.{Functional}
    use Fixpoint.Ast.Datalog.BodyPredicate.{Guard0, Guard1, Guard2, Guard3, Guard4, Guard5}
    use Fixpoint.Ast.Shared.Denotation
    use Fixpoint.Ast.Shared.isRelational
    use Fixpoint.Ast.Shared.PredSym
    use Fixpoint.Ast.Shared.PredSym.PredSym
    use PredTrack.{PredSymMapInternal}
    use PredTrack.PredType.{Full, Delta, New}


    pub type alias FixInformation = Map[PredSym, Int64]

    @Internal
    pub def fixPredSyms(d: Datalog): (Datalog, FixInformation) = match d {
        case Datalog(facts, rules) => region rc {
            let predToID = MutMap.empty(rc);
            let counter = Ref.fresh(rc, 0i64);
            let transformer = mapForward(counter, predToID);
            (Datalog(remapConstraints(facts, transformer), remapConstraints(rules, transformer)), MutMap.toMap(predToID))
        }
        case _ => bug!("PredSym error")
    }

    @Internal
    pub def unfixPredSym(d: Datalog, forwardMap: FixInformation): Datalog = match d {
        case Datalog(facts, rules) => 
            let transformer = mapBack(swapMapOrder(forwardMap));
            Datalog(remapConstraints(facts, transformer), remapConstraints(rules, transformer))
        case Model(map) => 
            let transformer = mapBack(swapMapOrder(forwardMap));
            Map.foldLeftWithKey(newMap -> k -> v -> match k {
                case RelSym.Symbol(p, arity, den) => Map.insert(RelSym.Symbol(transformer(p), arity, den), v, newMap)
            }, Map#{}, map)
            |> Model
        case _ => bug!("Bad argument of type 'Join' in PredSym renaming")
    }
    
    @Internal
    def mapBack(idToPred: Map[Int64, PredSym], pred: PredSym): PredSym = 
        let PredSym(_, id) = pred;
        match Map.get(id, idToPred) {
            case Some(v) => v
            case _ => bug!("Incomplete mapping given to when 'unfixing predicates'")
        }
    

    // @Internal
    // def mapBack(pred: PredSym, idToPred: Map[Int64, PredSym]): PredSym = 
    //     let PredSym(_, id) = pred;  
    //     match Map.get(id, idToPred) {
    //         case Some(v) => v
    //         case _ => bug!("Incomplete mapping given to when 'unfixing predicates'")
    //     }

    @Internal 
    def swapMapOrder(forwardMap: Map[PredSym, Int64]): Map[Int64, PredSym] = 
        Map.foldLeftWithKey(map -> k -> v -> Map.insert(v, k, map), Map#{}, forwardMap)

    // def mapReverse()

    @Internal
    def mapForward(counter: Ref[Int64, r], predToID: MutMap[PredSym, Int64, r], pred: PredSym): PredSym \ r = 
        let PredSym(name, _) = pred;
        match MutMap.get(pred, predToID) {
            case None => 
                let newID = Ref.get(counter); 
                Ref.put(newID + 1i64, counter); 
                MutMap.put(pred, newID, predToID); 
                PredSym(name, newID)
            case Some(v) => PredSym(name, v)
        }
    

    @Internal
    def remapConstraints(constraints: Vector[Constraint], transformer: PredSym -> PredSym \ r): Vector[Constraint] \ r = {
        Vector.map(match Constraint(head, body) -> Constraint(remapHead(head, transformer), Vector.map(x -> remapBody(x, transformer), body)), constraints)
    }

    @Internal
    def remapHead(head: HeadPredicate, transformer: PredSym -> PredSym \ r): HeadPredicate \ r = match head {
        case HeadAtom(pred, den, terms) => HeadAtom(transformer(pred), den, terms)
    }
    
    @Internal
    def remapBody(body: BodyPredicate, transformer: PredSym -> PredSym \ r): BodyPredicate \ r = match body {
        case BodyAtom(pred, den, pol, fixed, terms) => BodyAtom(transformer(pred), den, pol, fixed, terms)
        case _ => body
    }

    // @Internal
    // def remapPred(pred: PredSym, transformer: PredSym -> PredSym \ r): PredSym \ r = match pred {
    //     case PredSym(name, _) => match MutMap.get(pred, predToID) {
    //         case None => let newID = Ref.get(counter); Ref.put(newID + 1i64, counter); MutMap.put(pred, newID, predToID); PredSym(name, newID)
    //         case Some(v) => PredSym(name, v)
    //     }
    // }
}