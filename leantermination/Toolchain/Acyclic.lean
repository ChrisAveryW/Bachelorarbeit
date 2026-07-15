import leantermination.Datastructures.IntegerProgram
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate

open Function

-- this is the certificate, that determines if it is acyclic or not.
/-
Functionality:
This is topological ordering: every location receives a level, every sucessor of a transition must
have a greater level. If this holds it is acyclic. If it doesn't hold it isn't:
layer of t.src < layer of t.tgt < layer of t.src <-> layer of t.src < layer of t.src -> contrad.

In this case: Layering can be anykind of function that fulfills this property, to be acyclic.
But it is initialized with the max length from the initial location,
as this is a correct strict topological order.
-/

abbrev Layering := Nat → Nat

-- we use decide, since "<" is Prop.
-- checks if the acyclic invariant is given for all edges
def checkAcyclic (ip : IntegerProgram) (comp : Layering) : Bool :=
  ip.edges.all (fun t => decide (comp t.src < comp t.tgt))

-- this is the beginning of the proof, which formulates checkAcyclic as the Acyclic proof
lemma checkAcyclic_edge {ip : IntegerProgram} {comp : Layering}
    (h : checkAcyclic ip comp = true) :
    ∀ t ∈ ip.edges, comp t.src < comp t.tgt := by
  intro t ht
  have hb := (List.all_eq_true.mp h) t ht
  simpa using hb

-- uses definition of syntactic path to form into usable equation
lemma checkAcyclic_layer_mono {ip : IntegerProgram} {comp : Layering}
    (hedge : ∀ t ∈ ip.edges, comp t.src < comp t.tgt)
    {u v : Nat} (p : SyntacticPath ip u v) :
    comp u + p.length ≤ comp v := by
  induction p with
  | nil u h => simp [SyntacticPath.length]
  | cons t h p' ih =>
      -- u = t.src ; p' : SyntacticPath ip t.tgt v ; length = 1 + p'.length
      have hlt := hedge t h            -- comp t.src < comp t.tgt
      simp only [SyntacticPath.length]
      -- goal: comp t.src + (1 + p'.length) ≤ comp v ;  ih: comp t.tgt + p'.length ≤ comp v
      omega

-- soundness of layer certificate proven
theorem checkAcyclic_sound {ip : IntegerProgram} {comp : Layering}
    (h : checkAcyclic ip comp = true) : IntegerProgram.Acyclic ip := by
  unfold IntegerProgram.Acyclic
  intro u p
  have hmono := checkAcyclic_layer_mono (checkAcyclic_edge h) p  -- comp u + p.length ≤ comp u
  omega

-- computing the layering
-- bellman-ford relaxation
private def relaxOnce (edges : List Transition) (comp : Nat → Nat) : Nat → Nat :=
  edges.foldl
    (fun c t => Function.update c t.tgt (max (c t.tgt) (c t.src + 1)))
    comp


-- relax max locations + 1 times
def computeLayering (ip : IntegerProgram) : Layering := Id.run do
  let mut comp : Nat → Nat := fun _ => 0
  for _ in List.range (ip.locs.length + 1) do
    comp := relaxOnce ip.edges comp
  return comp

-- function that can be called, to determine acyclicity
def IntegerProgram.isAcyclic (ip : IntegerProgram) : Bool :=
  checkAcyclic ip (computeLayering ip)

-- final soundness theorem
-- this is not iff, it is oneway which should suffices for correctness but not completeness.
theorem IntegerProgram.isAcyclic_sound {ip : IntegerProgram}
    (h : ip.isAcyclic = true) : IntegerProgram.Acyclic ip :=
  checkAcyclic_sound h
