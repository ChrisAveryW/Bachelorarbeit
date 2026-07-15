import leantermination.Toolchain.Acyclic

set_option linter.unusedVariables false

def IntegerProgram.withoutSelfLoops (ip : IntegerProgram) : IntegerProgram :=
  {locs := ip.locs, l₀ := ip.l₀, edges := ip.edges.filter (fun t => t.src != t.tgt),
   h_edges := fun t ht => ip.h_edges t (List.mem_of_mem_filter ht)}

def checkAcyclicUpToSelfLoops (ip : IntegerProgram) (comp : Layering) : Bool :=
  ip.edges.all (fun t => (t.src == t.tgt) || decide (comp t.src < comp t.tgt))

-- function to determine acyclic up to linear self loops
def IntegerProgram.isAcyclicUpToSelfLoops (ip : IntegerProgram) : Bool :=
  checkAcyclicUpToSelfLoops ip (computeLayering ip.withoutSelfLoops)
