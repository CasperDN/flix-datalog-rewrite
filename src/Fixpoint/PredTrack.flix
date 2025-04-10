
/**
Purpose: We need to make more predicates (at most 3 times as many) than there are relations.
Solution: The first n are the full relations, the next n are the delta relations, the last n are the temporary delta' relations.
Problem: Assuming that the relations are currently named 0 to n seems restrictive
Solution: Start by creating a map from old relation-numbers to new.
    Advantage: If we were to change this later we would only have to change the module PredTrack. All other code does not need to care for the implementation.
 */

// Purpose: We need to make more predicates than there are 
mod PredTrack {
    use PredTrack.PredType
        use Fixpoint.Ast.Shared.PredSym
        use Fixpoint.Ast.Shared.PredSym.PredSym
        use Fixpoint.Ast.Datalog.Datalog.Datalog
        use Fixpoint.Ast.Datalog.{Datalog, Constraint, BodyPredicate, BodyTerm, HeadTerm, Polarity, VarSym}
        use Fixpoint.Ast.Datalog.Constraint.Constraint
        use Fixpoint.Ast.Datalog.HeadPredicate.HeadAtom
        use Fixpoint.Ast.Datalog.BodyPredicate.{BodyAtom}
        use Fixpoint.Ast.Ram.{RamStmt, RelOp, RelSym, RamTerm, BoolExp, RowVar, Facts, PredicateState, RamProgram}

        // (max+1, map from old index to RelSym, map from new index to old PredSym)
        pub type alias PredSymMapInternal = (Int64, Map[Int64, RelSym], Map[Int64, PredSym])

        pub enum PredType with Eq {
            case Full,
            case Delta,
            case New
        }
        pub def initialize(program: Datalog): PredSymMapInternal = 
            let (max, forwardMap) = remapAllPredicates(program);
            // let backMap = MutMap.empty(rc);
            let backMap = Map.mapWithKey(id -> v -> 
                match v {
                    case RelSym.Symbol(PredSym(name, _), _, _) => PredSym(name, id)
                }
            , forwardMap);
            (max, forwardMap, backMap)
        
        // pub def allRelSyms(predTrack: PredSymMapInternal): List[RelSym] =
        //     let (max, forwardMap, _) = predTrack;
        //     Map.foldLeftWithKey(acc -> _ -> relSym -> match relSym {
        //         case RelSym.Symbol(PredSym.PredSym(name, id), arity, den) => 
        //             List.foldLeft(acc1 -> counter -> 
        //                 RelSym.Symbol(PredSym.PredSym(name, id + counter), arity, den) :: acc1
        //             , acc, 0i64 :: max :: max * 2i64 :: Nil)
        //     }, Nil, forwardMap)

        pub def allFullRelSyms(predTrack: PredSymMapInternal): List[RelSym] =
            let (_, forwardMap, _) = predTrack;
            Map.foldLeftWithKey(acc -> _ -> relSym -> 
                relSym :: acc
            , Nil, forwardMap)


        pub def isFullPredicate(self: PredSymMapInternal, pred: PredSym): Bool = match pred {
            case PredSym(_, id) => isFullID(self, id)
        }

        pub def isFullID(self: PredSymMapInternal, id: Int64): Bool = 
            PredType.Full == idToPredType(self, id)

        pub def idToPredType(self: PredSymMapInternal, id: Int64): PredType = 
            let (max, _, _) = self;
            if(id <= max) {
                PredType.Full
            } else if (id <= max * 2i64) {
                PredType.Delta
            } else {
                PredType.New                
            }

        // Could use previos method, but would duplicate computation... 
        pub def idToFullPredID(id: Int64, self: PredSymMapInternal): Int64 =
            let (max, _, _) = self;
            if(id <= max) {
                id
            } else if (id <= max * 2i64) {
                id - max
            } else {
                id - 2i64 * max
            }


        // Could use previos method, but would duplicate computation... 
        pub def fullIDtoPredType(id: Int64, wantedType: PredType, self: PredSymMapInternal): Int64 =
            let (max, _, _) = self; match wantedType {
                case PredType.Full => id
                case PredType.Delta => id + max
                case PredType.New => id + max * 2i64
            }
            // if(id <= max) {
            //     id
            // } else if (id <= max * 2i64) {
            //     id - max
            // } else {
            //     id - 2i64 * max
            // }


        ///
        /// Collect all predicate symbols in a map

        ///
        def remapAllPredicates(program: Datalog): (Int64, Map[Int64, RelSym]) = match program {
            case Datalog(facts, rules) =>
                let (map1, max1) = collectPredicates(rules);
                let (map2, max2) = collectPredicates(facts);
                (Int64.max(max1, max2), Map.union(map1, map2))
            case _ => bug!("Datalog Boxing bug")
        }
        def collectPredicates(constraints: Vector[Constraint]): (Map[Int64, RelSym], Int64) = 
            // Missing Java's computeIfAbsent...

            Vector.foldLeft(mapMax -> constraint -> {match constraint { case Constraint(HeadAtom(PredSym(headName, headID), den, terms), body) =>
                let (map, max) = mapMax;
                let mapWithHead = Map.insert(headID, RelSym.Symbol(PredSym(headName, headID), Vector.length(terms), den), map);
                // (mapWithHead, max)
                Vector.foldLeft(mapMaxBody -> bodyConstraint -> 
                    let (mapBody, maxBody) = mapMaxBody;
                    match bodyConstraint {
                        case BodyAtom(PredSym(bodyName, bodyPred), bodyDen, _, _, bodyTerms) => (Map.insert(bodyPred, RelSym.Symbol(PredSym(bodyName, bodyPred), Vector.length(bodyTerms), bodyDen), mapBody), maxBody)
                        case _ => (mapBody, maxBody)
                    }, (mapWithHead, Int64.max(headID, max)), body)
                // (map, max)
            }}, (Map#{}, 0i64), constraints)
        pub def getNewID(self: PredSymMapInternal, predSym: PredSym, t: PredType): Int64 = match oldPredSymToPredSym(self, predSym, t) {
            case PredSym(_, id) => id
        }

        pub def getNewPred(self: PredSymMapInternal, predSym: PredSym, t: PredType): PredSym =
            oldPredSymToPredSym(self, predSym, t) 


        // pub def oldIDSymToPredSym(self: PredSymMapInternal, id: Int64, t: PredType): PredSym = match oldIDSymToRelSym(self, id, t) {
        //     case RelSym.Symbol(pred, _, _) => pred
        // }

        def oldPredSymToPredSym(self: PredSymMapInternal, predSym: PredSym, t: PredType): PredSym = match getNewRel(self, predSym, t) {
                case RelSym.Symbol(pred, _, _) => pred

        }

        pub def getNewRel(self: PredSymMapInternal, predSym: PredSym, t: PredType): RelSym = match predSym {
            case PredSym(_, id) => oldIDSymToRelSym(self, id, t)
        }

        pub def oldIDSymToRelSym(self: PredSymMapInternal, id: Int64, t: PredType): RelSym = 
            let (max, map, _) = self;
            let new_ = oldIDSymToNewRelSymInternal(id, map);
            match t {
                case PredType.Full => new_
                case PredType.Delta => addToRelSym(new_, max)
                case PredType.New => addToRelSym(new_, 2i64 * max)
        }


        @Internal
        def addToRelSym(relSym: RelSym, c: Int64): RelSym = match relSym {
            case RelSym.Symbol(pred, arity, den) => RelSym.Symbol(addToPredSym(pred, c), arity, den)
        }

        @Internal
        def addToPredSym(relSym: PredSym, c: Int64): PredSym = match relSym {
            case PredSym(name, id) => PredSym(name, id + c)
        }
        
        @Internal
        def oldIDSymToNewRelSymInternal(id: Int64, map: Map[Int64, RelSym]): RelSym = match Map.get(id, map) {
                case Some(relSym) => relSym
                case None => bug!("PredSymMap not initialized correctly?")
        }
    }
