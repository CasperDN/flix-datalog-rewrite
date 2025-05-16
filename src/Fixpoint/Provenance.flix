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

mod Fixpoint.Provenance {
    use Fixpoint.Ast.Datalog.Datalog
    use Fixpoint.Ast.Datalog.Datalog.{Datalog, Model, Join, Provenance}
    use Fixpoint.Ast.Ram.{RelSym}
    use Fixpoint.Boxed

    type alias ProvIDB = Map[RelSym, Map[Vector[Boxed], (Int64, Int32)]]

    enum ProofTree {
        case EDB(Vector[Boxed])
        case IDB(Vector[Boxed], Vector[ProofTree])
    }

    def provQuery(relSym: RelSym, fact: Vector[Boxed], d: Datalog): Option[List[Vector[Boxed]]] = match d {
        case Provenance(rules, provIdb) => {
            let reorderedRules = Vector.map(???, rules);
            let annotation = match Map.get(relSym, provIdb) {
                case None => None
                case Some(v) => match Map.get(fact, v) {
                    case None => None
                    case Some(annotations) => Some(annotations)
                }
            };
            match annotation {
                case None => None
                case Some((depth, ruleUsed)) => 
                    let tree = buildProof(relSym, fact, depth, ruleUsed, reorderedRules, provIdb);
                    ???
            }
        }
        case _ => 
            bug!("In Fixpoint.Provenance.provQuery: Can only build a proof from a provenance model")
    }

    def buildProof(relSym: RelSym, fact: Vector[Boxed], depth: Int64, ruleUsed: Int32, rules: ???, provIdb: ProvIDB): ProofTree = {
        let rule = Vector.get(ruleUsed, rules);
        ???
    }

}
