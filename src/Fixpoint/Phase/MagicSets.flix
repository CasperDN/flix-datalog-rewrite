/**
To avoid making a complete duplicate of Datalog.flix adopt the following way:
Rules are quadriples consisting of (headAtom, headAdorn, bodyAtoms, bodyAdorns)
Adornments are simple vectors of true/false depending on whether they are free (false) or bound (true)
*/

mod Fixpoint.Phase.MagicSets {
    use Fixpoint.Ast.Datalog.{Datalog, Constraint, BodyPredicate, BodyTerm, HeadTerm, Polarity, Fixity, VarSym, HeadTerm}
    use Fixpoint.Ast.Datalog.Datalog.{Datalog}
    use Fixpoint.Ast.Datalog.Constraint.Constraint
    use Fixpoint.Ast.Datalog.HeadPredicate.HeadAtom
    use Fixpoint.Ast.Datalog.HeadPredicate
    use Fixpoint.Ast.Datalog.BodyPredicate.{Guard0, Guard1, Guard2, Guard3, Guard4, Guard5, Functional, BodyAtom}
    use Fixpoint.Ast.Shared.{Denotation, isRelational, PredSym}
    use Fixpoint.Ast.Shared.PredSym.PredSym

    type alias Adornment = Vector[Bool]

    type alias IsMagic = Bool

    type alias AdornedAtom = (PredSym, Adornment, IsMagic)

    type alias AdornedHead = (HeadPredicate, Adornment, IsMagic)

    type alias AdornedBody = (BodyPredicate, Adornment, IsMagic)

    type alias InternalProgram = Map[PredSym, Vector[Vector[BodyPredicate]]]

    type alias AdornedRule = (HeadPredicate, Adornment, Vector[BodyPredicate], Vector[Adornment], SIP)

    // TODO: Temp type alias.
    type alias SIP = Int32

    pub def magicTransform(d: Datalog, query_: HeadPredicate): Option[Int32] = match d {
        case Datalog(facts, rules) => region rc {
            let (adornedQuery, newRules) = adornmentAlg(rules, query_, rc);
            ???
        }
        case _ => bug!("Datalog Boxing bug")
    }

    def adornmentAlg(program: Vector[Constraint], query_: HeadPredicate, rc: Region[r]): (AdornedHead, Vector[AdornedRule]) \ r = {
        let programTemp: MutMap[PredSym, List[Vector[BodyPredicate]], r] = MutMap.empty(rc);
        // HeadPredicate, Vector[BodyPredicate]
        program |>
        Vector.forEach(match Constraint(HeadAtom(pred, _, _), body) -> 
            MutMap.putWith(_ -> old -> body :: old, pred, body :: Nil, programTemp)
        );
        let programAsMap = programTemp |>
            MutMap.map(rc, List.toVector) |>
            MutMap.toMap;
        let adornedHead = adornBy(query_);
        let seen = MutSet.empty(rc);
        MutSet.add(adornedHead, seen);
        let newProgram = MutList.empty(rc);
        let workList = MutList.empty(rc);
        MutList.push(adornedHead, workList);
        adornmentLoop(rc, programAsMap, workList, seen, newProgram);
        let (_, queryAdornment, _) = adornedHead;
        ((query_, queryAdornment, false), MutList.toVector(newProgram))
    }

    // TODO: Add Sips.
    // TODO: Remove the ;\n () pattern. They were used for debugging.
    def adornmentLoop(rc: Region[r], program: InternalProgram, workList: MutList[AdornedAtom, r], seen: MutSet[AdornedAtom, r], newProgram: MutList[AdornedRule, r]): Unit \ r = match MutList.pop(workList) {
        case None => ()
        case Some((pred, adorn, magic)) => match Map.get(pred, program) {
            case None => adornmentLoop(rc, program, workList, seen, newProgram)
            case Some(ruleBodies) =>
                let adornedHead = (pred, adorn, false);
                ruleBodies |>
                Vector.forEach(ruleBody -> {
                    let (bodyAndAdorn, sip) = adornWithSip(adornedHead, ruleBody);
                    addNewAtoms(workList, seen, bodyAndAdorn);
                    let (newBodyList, bodyAdornsList) = Vector.foldLeft(match (bodyList, adornmentList) -> match (bodyElem, adornment) ->
                        (bodyElem :: bodyList, adornment :: adornmentList)
                    , (Nil, Nil), bodyAndAdorn);
                    let newBody = List.toVector(newBodyList);
                    let bodyAdorns = List.toVector(bodyAdornsList);
                    MutList.push((???, adorn, newBody, bodyAdorns, sip), newProgram);
                    ()
                });
                adornmentLoop(rc, program, workList, seen, newProgram);
                ()
        }
    }

    def magicTransformHead(adornedAtom: AdornedHead): AdornedHead = {
        let (headPred, adornment, _) = adornedAtom;
        let HeadAtom(pred, den, headTerms) = headPred;
        let newTerms = magicTransformTerms(headTerms, adornment);
        (HeadAtom(pred, den, newTerms), adornment, true)
    }

    def magicTransformBody(adornedAtom: AdornedBody): AdornedBody = match adornedAtom {
        case (BodyAtom(pred, den, pol, fixity, headTerms), adornment, _) =>
            let newTerms = magicTransformTerms(headTerms, adornment);
            (BodyAtom(pred, den, pol, fixity, newTerms), adornment, true)
        case _ => bug!("So far this should not handle these cases")
    }

    // This function could be optimized to create fewer vectors (it creates 3)
    def magicTransformTerms(terms: Vector[a], choices: Vector[Bool]): Vector[a] = {
        terms |> 
        Vector.mapWithIndex(i -> term -> 
            if(Vector.get(i, choices)) Some(term) 
            else None
        ) |>
        Vector.filter(Option.nonEmpty) |>
        Vector.map(Fixpoint.Helpers.unwrap)
    }


    def addNewAtoms(workList: MutList[AdornedAtom, r], seen: MutSet[AdornedAtom, r], newBody: Vector[(BodyPredicate, Adornment)]): Unit \ r =
        newBody |>
        Vector.forEach(x -> match x {
            case (BodyAtom(pred, _, _, _, _), adornment) =>
                let maybeNewAtom = (pred, adornment, false);
                if(MutSet.memberOf(maybeNewAtom, seen)) ()
                else
                    MutList.push(maybeNewAtom, workList);
                    MutSet.add(maybeNewAtom, seen)
            case _ => ()
        })
    

    def adornWithSip(head: AdornedAtom, body: Vector[BodyPredicate]): (Vector[(BodyPredicate, Adornment)], SIP) = ???

    def adornBy(headAtom: HeadPredicate): AdornedAtom = match headAtom {
        case HeadAtom(pred, _, terms) => (pred, headTermToAdorn(terms), false)
    }

    def headTermToAdorn(terms: Vector[HeadTerm]): Adornment =
        terms |> Vector.map(x -> match x {
            case HeadTerm.Lit(_) => true
            case _ => false
        })
}