import leantermination.Parsing.ITSParse
import leantermination.Parsing.Preparse
import leantermination.Termination.AcyclicIntegerProgram
import leantermination.Toolchain.Acyclic
import leantermination.Toolchain.AcyclicUpToSelfLoops
import leantermination.Toolchain.FarkasSMT

set_option linter.unusedVariables false
set_option linter.style.longLine false


def reportUpToSelfLoops (ip : IntegerProgram) : IO Unit := do
  if ip.isAcyclicUpToSelfLoops then
    IO.println "Integer Program is acyclic up to self-loops"
    let results ← ip.checkSelfLoops
    if results.isEmpty then
      IO.println "No self-loops: the program is fully acyclic."
    else
      IO.println s!"Querying Z3 for a linear ranking function of each of the {results.length} self-loops:"
      for (t, r) in results do
        IO.println s!"  Self-loop at location {t.src}: {r.toString}"
    let allRank := results.all (fun (_, r) => r == Z3Result.sat)
    if allRank then
      IO.println "==> Every self-loop admits a linear ranking function. The program terminates."
    else
      IO.println "==> Some self-loop has no linear ranking function; termination could not be proven."
  else
    IO.println "==> Program is not acyclic up to self-loops. Result unknown. "

/-- Read an ITS file, parse it, and run the whole acyclic-up-to-self-loops
    termination pipeline on it. -/
def checkFileUpToSelfLoops (path : String) : IO Unit := do
  let input ← IO.FS.readFile path
  match parseITS input with
  | some ip => reportUpToSelfLoops ip
  | none    => IO.println "Failed to parse ITS file"

def main : IO Unit :=
  checkFileUpToSelfLoops "leantermination/Data/IntegerPrograms/Acyclic/Test2.ari"
