/*
 * Copyright 2021 Magnus Madsen
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

mod Fixpoint.Debugging {

    use Fixpoint.Ast.Datalog.Datalog
    // use Fixpoint.Ast.Ram.RamStmt
    // use Fixpoint.Ast.Ram.RamProgram
    use Fixpoint.Ast.ExecutableRam.RamProgram
    use Fixpoint.Ast.Shared.PredSym

    def flush(s: String, overwrite: Bool): Unit \ IO = 
        if (Fixpoint.Options.enableDebugToFile()) {
            let res = 
                if (overwrite) 
                    FileWrite.runWithIO(() -> FileWrite.write(str = s, debugFileName()))
                else 
                    FileWrite.runWithIO(() -> FileWrite.append(str = s, debugFileName()));
            match res {
                case Ok(_) => ()
                case Err(e) => println(e)
            } 
        } else println(s)

    def debugFileName(): String = ".fixpoint_debug.txt" 

    def concatRev(s1: String, s2: String): String = String.concat("${s2}\n", s1)

    ///
    /// Invoked before the fixpoint computation.
    ///
    /// Note: Returns `d` to ensure it is not erased.
    ///
    @Internal
    pub def notifyPreSolve(d: Datalog): Datalog = unchecked_cast({
        if (Fixpoint.Options.enableDebugging()) {
            let str = String.repeat(80, "*") |>
                concatRev("** Datalog Input") |>
                concatRev(String.repeat(80, "*")) |>
                concatRev("") |>
                concatRev(String.indent(4, "${d}")) |>
                concatRev("");
            flush(str, true);
            d
        } else {
            d
        }
    } as _ \ {})

    ///
    /// Invoked with the minimal model of the fixpoint computation.
    ///
    /// Note: Returns `d` to ensure it is not erased.
    ///
    @Internal
    pub def notifyPostSolve(d: Datalog): Datalog = unchecked_cast({
        if (Fixpoint.Options.enableDebugging()) {
            let str = String.repeat(80, "*") |>
                concatRev("** Minimal Model") |>
                concatRev(String.repeat(80, "*")) |>
                concatRev("") |>
                concatRev(String.indent(4, "${d}")) |>
                concatRev("");
            flush(str, false);
            d
        } else {
            d
        }
    } as _ \ {})

    ///
    /// Invoked before the fixpoint computation.
    ///
    /// Note: Returns `s` to ensure it is not erased.
    ///
    @Internal
    pub def notifyPreInterpret(program: RamProgram): RamProgram = match program {
        case RamProgram.Program(stmt, facts, _meta, index) => unchecked_cast({
            if (Fixpoint.Options.enableDebugging()) {
                let str = String.repeat(80, "*") |>
                concatRev("** Facts") |>
                concatRev(String.repeat(80, "*")) |>
                concatRev("") |>
                concatRev(String.indent(4, "${unchecked_cast(facts as Map[Int64, Vector[Vector[Fixpoint.Boxed]]])}")) |>
                concatRev(String.indent(4, "${Debug.stringify(facts)}")) |>
                concatRev("") |>
                concatRev(String.repeat(80, "*")) |>
                concatRev("** Relation Algebra Machine AST") |>
                concatRev(String.repeat(80, "*")) |>
                concatRev("") |>                
                concatRev(String.indent(4, "${stmt}")) |>
                concatRev("") |>
                concatRev(String.repeat(80, "*")) |>
                concatRev("** Index Information") |>
                concatRev(String.repeat(80, "*")) |>
                concatRev("") |>
                concatRev(String.indent(4, Map.joinWith(k -> v -> "${k}: ${v}", "\n", index))) |>
                concatRev("");
                flush(str, false);
                program
            } else {
                program
            }
        } as _ \ {})
    }

}
