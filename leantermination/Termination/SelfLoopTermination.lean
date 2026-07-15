import leantermination.Datastructures.IntegerProgram
import leantermination.Termination.LASWTermination
import leantermination.Termination.AcyclicIntegerProgram
import leantermination.Toolchain.Acyclic
import leantermination.Toolchain.AcyclicUpToSelfLoops
import Mathlib.Tactic

open LASW



namespace IntegerProgram
--TODO DELETE REDUNDANT
def selfLoops (ip : IntegerProgram) : List Transition :=
  ip.edges.filter (fun t => t.src == t.tgt)

def AcyclicUpToSelfLoops (ip : IntegerProgram) : Prop :=
  IntegerProgram.Acyclic ip.withoutSelfLoops

-- check if needed, can delete @todo
def transition_to_ip (ip : IntegerProgram) (t : Transition)
    (h_self : t.src = t.tgt) (h_edge : t ∈ ip.edges) : IntegerProgram :=
  { locs := [t.src],
    l₀ := t.src,
    edges := [t],
    h_edges := by
      intro tq htq
      rw [List.mem_singleton] at htq
      rw [htq, h_self]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      trivial }

end IntegerProgram


namespace SemanticPath

def usesOnly {ip : IntegerProgram} (t : Transition) :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v → Prop
  | _, _, _, .nil _ _ _ => True
  | _, _, _, .cons _ t' _ _ _ _ p => t' = t ∧ p.usesOnly t

def selfLoopSteps {ip : IntegerProgram} :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v → Nat
  | _, _, _, .nil _ _ _          => 0
  | _, _, _, .cons _ t _ _ _ _ p =>
      (if t.src = t.tgt then 1 else 0) + selfLoopSteps p

def skeletonSteps {ip : IntegerProgram} :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v → Nat
  | _, _, _, .nil _ _ _          => 0
  | _, _, _, .cons _ t _ _ _ _ p =>
      (if t.src = t.tgt then 0 else 1) + skeletonSteps p

def skeletonProject {ip : IntegerProgram} :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v →
      SyntacticPath ip.withoutSelfLoops u v
  | _, u, _, .nil _ _ h => .nil u (by
      -- u ∈ ip.locs  →  u ∈ withoutSelfLoops.locs (same locs)
      simpa [IntegerProgram.withoutSelfLoops] using h)
  | _, _, v, .cons env t h_edge hguard env' hupdate p =>
      if hsl : t.src = t.tgt then
        -- self-loop: skip this step. But its tgt = src, so the recursive
        -- projection of p (which starts at t.tgt = t.src) lands at the same u.
        hsl ▸ (skeletonProject p)   -- needs care: rewrite t.tgt = t.src
      else
        -- skeleton edge: keep it. Need t ∈ withoutSelfLoops.edges.
        .cons t (by
          -- t ∈ ip.edges ∧ t ∉ selfLoops  →  t ∈ withoutSelfLoops.edges
          simp only [IntegerProgram.withoutSelfLoops, IntegerProgram.selfLoops, List.mem_filter,
            decide_eq_true_eq, not_and, decide_implies, decide_not, dite_eq_ite, Bool.if_true_right,
            Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
          exact ⟨h_edge, Or.inr hsl⟩) (skeletonProject p)

lemma SyntacticPath.length_cast {ip : IntegerProgram} {u u' v : Nat}
    (h : u = u') (p : SyntacticPath ip u v) :
    (h ▸ p).length = p.length := by
  subst h; rfl

lemma skeletonProject_length {ip : IntegerProgram}
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    p.skeletonProject.length = p.skeletonSteps := by
  induction p with
  | nil _ _ _ => rfl
  | cons env t h_edge hguard env' hupdate p' ih =>
      simp only [SemanticPath.skeletonProject, SemanticPath.skeletonSteps]
      split_ifs with hsl
      · simp only [zero_add]
        rw [SyntacticPath.length_cast]
        exact ih
      · -- skeleton kept: both add 1
        simp [SyntacticPath.length]
        omega


end SemanticPath

/-- Length splits into self-loop + skeleton steps. (Provable; see prior scaffold.) -/
lemma length_eq_selfloop_add_skeleton
    {ip : IntegerProgram} {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    p.length = p.selfLoopSteps + p.skeletonSteps := by
  induction p with
  | nil u env h =>
      rfl
  | cons env t h_edge hguard env' hupdate p' ih =>
      simp only [SemanticPath.length, SemanticPath.selfLoopSteps,
                 SemanticPath.skeletonSteps]
      rw [ih]
      split_ifs with h
      · omega
      · omega

/-- Skeleton steps bounded by number of locations (graph theory). -/
lemma skeleton_steps_bounded
    {ip : IntegerProgram} (h_upto : ip.AcyclicUpToSelfLoops)
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    p.skeletonSteps ≤ ip.locs.length := by
  -- h_upto : Acyclic withoutSelfLoops
  have h_bound := acyclic_impl_bounded_SyntacticPath h_upto p.skeletonProject
  -- h_bound : p.skeletonProject.length < withoutSelfLoops.locs.length
  rw [SemanticPath.skeletonProject_length] at h_bound
  -- withoutSelfLoops.locs = ip.locs (same locs field)
  have h_locs : ip.withoutSelfLoops.locs = ip.locs := rfl
  rw [h_locs] at h_bound
  omega



-- proof sketch
lemma selfloop_run_bounded
    {ip : IntegerProgram} {t : Transition}
    (h_self : t.src = t.tgt) (h_edge : t ∈ ip.edges)
    {n m : ℕ} (w : LASW.FarkasWitness n m)
    (h_repr : w.RepresentsProgram (ip.transition_to_ip t h_self h_edge))
    (env : Env) :
    ∃ N : Nat, ∀ {u v : Nat} (p : SemanticPath ip env u v),
      SemanticPath.usesOnly t p → p.length ≤ N := by
  sorry

-- proof sketch
lemma total_selfloop_steps_bounded
    {ip : IntegerProgram}
    (h_witnesses : ∀ t ∈ ip.selfLoops,
        ∃ (n m : ℕ) (w : LASW.FarkasWitness n m) (h_self : t.src = t.tgt) (h_edge : t ∈ ip.edges),
          w.RepresentsProgram (ip.transition_to_ip t h_self h_edge))
    (h_upto : ip.AcyclicUpToSelfLoops)
    (env : Env) :
    ∃ B : Nat, ∀ {u v : Nat} (p : SemanticPath ip env u v), p.selfLoopSteps ≤ B := by
  sorry

-- main theorem
theorem terminates_of_selfloops_rank
    {ip : IntegerProgram}
    (h_witnesses : ∀ t ∈ ip.selfLoops,
        ∃ (n m : ℕ) (w : LASW.FarkasWitness n m) (h_self : t.src = t.tgt) (h_edge : t ∈ ip.edges),
          w.RepresentsProgram (ip.transition_to_ip t h_self h_edge))
    (h_upto : IntegerProgram.AcyclicUpToSelfLoops ip) :
    ip.Termination := by
  intro env
  -- Get the uniform self-loop step bound B for paths from `env`.
  obtain ⟨B, hB⟩ := total_selfloop_steps_bounded h_witnesses h_upto env
  -- The uniform total bound: self-loop budget + skeleton budget.
  refine ⟨B + ip.locs.length, ?_⟩
  intro u v p
  -- Decompose the length.
  have h_split : p.length = p.selfLoopSteps + p.skeletonSteps :=
    length_eq_selfloop_add_skeleton p
  -- Bound each part.
  have h_sl : p.selfLoopSteps ≤ B := hB p
  have h_sk : p.skeletonSteps ≤ ip.locs.length := skeleton_steps_bounded h_upto p
  -- Combine.
  omega


-- ## Soundness of the checker


private lemma mem_withoutSelfLoops_edges
    {ip : IntegerProgram} {t : Transition}
    (ht : t ∈ ip.withoutSelfLoops.edges) : t ∈ ip.edges ∧ t.src ≠ t.tgt := by
  simp only [IntegerProgram.withoutSelfLoops, IntegerProgram.selfLoops,
    decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at ht
  aesop

-- main soundness theorem
theorem checkAcyclicUpToSelfLoops_sound
    {ip : IntegerProgram} {comp : Layering}
    (h : checkAcyclicUpToSelfLoops ip comp = true) :
    IntegerProgram.AcyclicUpToSelfLoops ip := by
  -- AcyclicUpToSelfLoops ip  ≡  Acyclic ip.withoutSelfLoops
  unfold IntegerProgram.AcyclicUpToSelfLoops
  apply checkAcyclic_sound (comp := comp)
  -- remaining goal: checkAcyclic ip.withoutSelfLoops comp = true
  unfold checkAcyclic
  rw [List.all_eq_true]
  intro t ht
  obtain ⟨ht_edge, ht_ne⟩ := mem_withoutSelfLoops_edges ht
  -- the per-edge disjunction for this (non-self-loop) edge of ip
  have hdisj := (List.all_eq_true.mp h) t ht_edge
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hdisj
  rcases hdisj with heq | hlt
  · exact absurd heq ht_ne          -- not a self-loop, so this disjunct is impossible
  · simpa using hlt                 -- hence the layer strictly increases

-- soundness, only one way completeness not given
theorem IntegerProgram.isAcyclicUpToSelfLoops_sound {ip : IntegerProgram}
    (h : ip.isAcyclicUpToSelfLoops = true) :
    IntegerProgram.AcyclicUpToSelfLoops ip :=
  checkAcyclicUpToSelfLoops_sound h
