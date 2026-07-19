import leantermination.Parsing.ITSParse
import leantermination.Parsing.Preparse
import leantermination.Termination.AcyclicIntegerProgram
import leantermination.Toolchain.Acyclic
import leantermination.Toolchain.AcyclicUpToSelfLoops
import leantermination.Toolchain.FarkasSMT

set_option linter.unusedVariables false
set_option linter.style.longLine false


/-- Present one location's *joint* synthesize-and-verify outcome. A single ranking
    function must cover *all* self-loops at the location; on `verified` we print it.
    (Per-location — not per-self-loop — is what makes the verdict sound: individual
    ranking functions do not rule out non-terminating interleavings.) -/
def describeLocCheck : LocCheck → String
  | .noLoops              => "no self-loops"
  | .unsupported          => "unsupported (non-linear / non-conjunctive) guard"
  | .noRank               => "unsat — no single ranking function covers all self-loops here"
  | .unknown              => "unknown — Z3 could not decide"
  | .solverError m        => s!"error: {m}"
  | .verified cert        => s!"sat — joint witness read back and verified ✓\n      {cert.rankingString}"
  | .modelUnverified _    => "sat, but the returned model FAILED the independent Farkas check ✗"

def reportUpToSelfLoops (ip : IntegerProgram) : IO Unit := do
  if ip.isAcyclicUpToSelfLoops then
    IO.println "Integer Program is acyclic up to self-loops"
    let results ← ip.checkSelfLoopLocationsWitness
    if results.isEmpty then
      IO.println "No self-loops: the program is fully acyclic."
    else
      IO.println s!"Synthesizing and verifying one joint ranking function per self-loop location ({results.length} location(s)):"
      for (l, r) in results do
        IO.println s!"  Location {l} ({(ip.selfLoopsAt l).length} self-loop(s)): {describeLocCheck r}"
    let allRank := results.all (fun (_, r) => r.isVerified)
    if allRank then
      IO.println "==> Every self-loop location has a verified joint ranking function. The program terminates."
    else
      IO.println "==> Some self-loop location has no verified joint ranking function; termination could not be proven."
  else
    IO.println "==> Program is not acyclic up to self-loops. Result unknown. "

/-- Read an ITS file, parse it, and run the whole acyclic-up-to-self-loops
    termination pipeline on it. -/
def checkFileUpToSelfLoops (path : String) : IO Unit := do
  let input ← IO.FS.readFile path
  match parseITS input with
  | some ip => reportUpToSelfLoops ip
  | none    => IO.println "Failed to parse ITS file"

def main (args : List String) : IO Unit :=
  let path := args.headD "leantermination/Data/IntegerPrograms/AcyclicUpto/Test2.ari"
  checkFileUpToSelfLoops path
