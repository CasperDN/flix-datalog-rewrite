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

///
/// The current implementation does not output the negative atoms. They can be derived from the positive.
///
mod Fixpoint.Provenance {
    use Fixpoint.Ast.Datalog.{Datalog, Constraint, VarSym, BodyPredicate, HeadPredicate, HeadTerm, BodyTerm, Polarity}
    use Fixpoint.Ast.Datalog.Datalog.{Datalog, Model, Join, Provenance}
    use Fixpoint.Ast.Shared.{PredSym}
    use Fixpoint.Boxed
    use Fixpoint.Util.getOrCrash

    type alias ProvIDB = Map[PredSym, Map[Vector[Boxed], (Int64, Int32)]]

    enum ProofTree {
        case EDB(PredSym, Vector[Boxed])
        case Negative(PredSym, Vector[Boxed])
        case IDB(PredSym, Vector[Boxed], Vector[ProofTree])
    }

    mod ProofTree {
        pub def toString(p: ProofTree, indentChild: Int32): String = match p {
            case EDB(pred, fact) => 
                let factString = Vector.join(", ", fact);
                "${pred}(${factString}). Fact"
            case Negative(pred, fact) => 
                let factString = Vector.join(", ", fact);
                "No ${pred}(${factString})"
            case IDB(pred, fact, subs) => 
                let subProofs = Vector.joinWith(sub -> toString(sub, indentChild + 4), String.lineSeparator(), subs);
                let factString = Vector.join(", ", fact);
                let indentCur = String.repeat(indentChild, " ");
                let indentString = String.repeat(indentChild + 4, " ");
                "${indentCur}${pred}(${factString}). Proof:${String.lineSeparator()}${indentString}${subProofs}"
        }
    }

    instance ToString[ProofTree] {
        pub def toString(p: ProofTree): String = ProofTree.toString(p, 0)
    }

    def flatMap(p: ProofTree): List[(PredSym, Vector[Boxed])] = region rc {
        let res = MutList.empty(rc);
        def recurse(t) = match t {
            case ProofTree.EDB(pred, fact) => MutList.push((pred, fact), res)
            case ProofTree.Negative(_, _) => ()
            case ProofTree.IDB(pred, fact, subTrees) => {
                MutList.push((pred, fact), res);
                subTrees |> Vector.forEach(recurse)
        }};
        recurse(p);
        res |> MutList.toList
    }

    pub def provQuery(predSym: PredSym, fact: Vector[Boxed], d: Datalog): Option[List[(PredSym, Vector[Boxed])]] = match d {
        case Provenance(rules, provIdb) => {
            let reorderedRules = Vector.map(identity, rules);
            let annotation = match Map.get(predSym, provIdb) {
                case None => None
                case Some(v) => match Map.get(fact, v) {
                    case None => None
                    case Some(annotations) => Some(annotations)
                }
            };
            match annotation {
                case None => None
                case Some((depth, ruleUsed)) => 
                    let tree = buildProof(predSym, fact, depth, ruleUsed, reorderedRules, provIdb);
                    unchecked_cast({println(tree); Some(flatMap(tree))} as _ \ {})
                    
            }
        }
        case _ => 
            bug!("In Fixpoint.Provenance.provQuery: Can only build a proof from a provenance model")
    }

    def buildProof(predSym: PredSym, fact: Vector[Boxed], depth: Int64, ruleUsed: Int32, rules: Vector[Constraint], provIdb: ProvIDB): ProofTree = {
        if(ruleUsed == -1) {
            ProofTree.EDB(predSym, fact)
        } else if(ruleUsed == -2) {
            ProofTree.Negative(predSym, fact)
        } else {
            let rule = Vector.get(ruleUsed, rules);
            let bodyAtoms = getMatchingBody(fact, depth, provIdb, rule);
            let Constraint.Constraint(_, bodyPreds) = rule;
            let relevantPreds = bodyPreds |> Vector.filter(bodyAtom -> match bodyAtom {
                case BodyPredicate.BodyAtom(_, _, _, _, _) => true
                case _ => false
            });
            let childProofs = Vector.zip(relevantPreds, bodyAtoms) |> Vector.map(match (bodyP, (bodyFact, bodyDepth, bodyRule)) -> match bodyP {
                case BodyPredicate.BodyAtom(p, _, _, _, _) =>
                    buildProof(p, bodyFact, bodyDepth, bodyRule, rules, provIdb)
                // case BodyPredicate.BodyAtom(_, _, Polarity.Negative, _, _) =>
                //     ProofTree.Negative(predSym, bodyFact)
                case _      => unreachable!()
            });
            ProofTree.IDB(predSym, fact, childProofs)
        }
    }

    def getMatchingBody(
        fact: Vector[Boxed],
        depth: Int64,
        provIdb: ProvIDB,
        rule: Constraint
    ): Vector[(Vector[Boxed], Int64, Int32)] = region rc {
        let Constraint.Constraint(HeadPredicate.HeadAtom(_, _, headTerms), bodyPreds) = rule;
        let bodyValues = Array.init(rc, _ -> None, Vector.length(bodyPreds));
        let getValOfVar = MutMap.empty(rc);
        let headApps = Vector.zip(headTerms, fact) |>
        Vector.filter(match (h, _) -> match h {
            case (HeadTerm.App0(_)) => false // Must be true.
            case (HeadTerm.App1(_, _)) => true
            case (HeadTerm.App2(_, _, _)) => true
            case (HeadTerm.App3(_, _, _, _)) => true
            case (HeadTerm.App4(_, _, _, _, _)) => true
            case (HeadTerm.App5(_, _, _, _, _, _)) => true
            case _ => false
        });

        def getVal(varName) = getOrCrash(MutMap.get(varName, getValOfVar));
        def putVals(bodyTerms, matchedVFact) = bodyTerms |> Vector.forEachWithIndex(i -> b -> match b {
            case BodyTerm.Wild => ()
            case BodyTerm.Lit(_) => ()
            case BodyTerm.Var(v) => MutMap.put(v, Vector.get(i, matchedVFact), getValOfVar)
        });
        let guardFromApp = () -> headApps |>
            Vector.forAll(match (app, val) -> match app {
                case (HeadTerm.App1(f, v1))                 => val == f(getVal(v1))
                case (HeadTerm.App2(f, v1, v2))             => val == f(getVal(v1), getVal(v2))
                case (HeadTerm.App3(f, v1, v2, v3))         => val == f(getVal(v1), getVal(v2), getVal(v3))
                case (HeadTerm.App4(f, v1, v2, v3, v4))     => val == f(getVal(v1), getVal(v2), getVal(v3), getVal(v4))
                case (HeadTerm.App5(f, v1, v2, v3, v4, v5)) => val == f(getVal(v1), getVal(v2), getVal(v3), getVal(v4), getVal(v5))
                case _ => unreachable!()
            });
        
        def loop(index) =
            if (index == Vector.length(bodyPreds)) {
                guardFromApp()
            } else {
                // This could, for performance something that was done once and only once. Would
                // require new representation.
                match Vector.get(index, bodyPreds) {
                    case BodyPredicate.BodyAtom(pred, _, Polarity.Positive, _, expected) =>
                        let (filterAsList, _) = expected |> Vector.foldLeft(match (acc, i) -> t -> match t {
                            case BodyTerm.Wild => (acc, i + 1)
                            case BodyTerm.Var(v) => match MutMap.get(v, getValOfVar) {
                                case None => (acc, i + 1)
                                case Some(val) => ((i, val) :: acc, i + 1)
                            }
                            case BodyTerm.Lit(val) => ((i, val) :: acc, i + 1)
                        }, (Nil, 0));
                        let filter = List.toVector(filterAsList);
                        match Map.get(pred, provIdb) {
                            case None => false
                            case Some(facts) => facts |> Map.exists(bodyFact -> match (bodyDepth, bodyRule) -> {
                                let matchingTuple = bodyDepth < depth and filter |> Vector.forAll(match (i, val) -> Vector.get(i, bodyFact) == val);
                                if(not matchingTuple) {
                                    false
                                } else {
                                    Array.put(Some((bodyFact, bodyDepth, bodyRule)), index, bodyValues);
                                    putVals(expected, bodyFact);
                                    loop(index + 1)
                                }
                            })
                        }
                    case BodyPredicate.BodyAtom(pred, _, Polarity.Negative, _, expected) =>
                        let vals = expected |> Vector.map(t -> match t {
                            case BodyTerm.Var(v) => getVal(v)
                            case BodyTerm.Lit(val) => val
                            case BodyTerm.Wild => unreachable!()
                        });
                        let isNonMatch = match Map.get(pred, provIdb) {
                            case None => true
                            case Some(facts) => not Map.memberOf(vals, facts)
                        };
                        if(not isNonMatch)
                            false
                        else {
                            // No need to save the match. Negative atoms cannot bind variables.
                            Array.put(Some((vals, -2i64, -2)), index, bodyValues);
                            loop(index + 1)
                        }
                    case BodyPredicate.Guard0(f) =>
                        if(f())
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard1(f, v1) =>
                        if(f(getVal(v1)))
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard2(f, v1, v2) =>
                        if(f(getVal(v1), getVal(v2)))
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard3(f, v1, v2, v3) =>
                        if(f(getVal(v1), getVal(v2), getVal(v3)))
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard4(f, v1, v2, v3, v4) =>
                        if(f(getVal(v1), getVal(v2), getVal(v3), getVal(v4)))
                            loop(index + 1)
                        else false
                    case BodyPredicate.Guard5(f, v1, v2, v3, v4, v5) =>
                        if(f(getVal(v1), getVal(v2), getVal(v3), getVal(v4), getVal(v5)))
                            loop(index + 1)
                        else false
                    // Functional in provenance is not supported.
                    case BodyPredicate.Functional(_, _, _) => unreachable!()
                }
            };
        headTerms |> Vector.mapWithIndex(i -> h -> match h {
            case HeadTerm.Var(v) => MutMap.put(v, Vector.get(i, fact), getValOfVar)
            case _ => ()
        });
        loop(0);
        bodyValues |> Array.filterMap(rc, identity) |> Array.toVector
    }
}
