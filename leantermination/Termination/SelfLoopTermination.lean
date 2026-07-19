import leantermination.Datastructures.IntegerProgram
import leantermination.Termination.LASWTermination
import leantermination.Termination.AcyclicIntegerProgram
import leantermination.Toolchain.Acyclic
import leantermination.Toolchain.AcyclicUpToSelfLoops
import Mathlib.Tactic

open LASW



namespace IntegerProgram
-- Todo redundant function, delete
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

/-- The single-location sub-program consisting of **all** self-loops at `l`.

    A Farkas witness for this program certifies that the (possibly disjunctive)
    loop at `l` terminates. This is the *correct* granularity for the termination
    theorem: a witness per *individual* self-loop does **not** rule out
    non-terminating interleavings of several self-loops at the same location
    (e.g. `x'=x-1,y'=y+1` and `x'=x+1,y'=y-1`, each terminating alone but jointly
    looping forever). -/
def selfloops_to_ip (ip : IntegerProgram) (l : Nat) : IntegerProgram :=
  { locs := [l],
    l₀ := l,
    edges := ip.edges.filter (fun t => t.src == l && t.tgt == l),
    h_edges := by
      intro t ht
      simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq] at ht
      obtain ⟨_, hsrc, htgt⟩ := ht
      rw [hsrc, htgt]
      simp }

/-- Membership in the edges of `selfloops_to_ip l`: exactly the self-loops at `l`. -/
lemma mem_selfloops_to_ip_edges {ip : IntegerProgram} {l : Nat} {t : Transition} :
    t ∈ (ip.selfloops_to_ip l).edges ↔ t ∈ ip.edges ∧ t.src = l ∧ t.tgt = l := by
  simp only [selfloops_to_ip, List.mem_filter, Bool.and_eq_true, beq_iff_eq]

end IntegerProgram


namespace SemanticPath

def usesOnly {ip : IntegerProgram} (t : Transition) :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v → Prop
  | _, _, _, .nil _ _ _ => True
  | _, _, _, .cons _ t' _ _ _ _ p => t' = t ∧ p.usesOnly t

/-- Every step of the path is a self-loop at location `l` (i.e. an edge of
    `selfloops_to_ip l`). Such a run stays at `l` throughout. -/
def usesLoopsAt {ip : IntegerProgram} (l : Nat) :
    ∀ {env : Env} {u v : Nat}, SemanticPath ip env u v → Prop
  | _, _, _, .nil _ _ _ => True
  | _, _, _, .cons _ t _ _ _ _ p => t.src = l ∧ t.tgt = l ∧ p.usesLoopsAt l

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
          -- t ∈ ip.edges ∧ t.src ≠ t.tgt  →  t ∈ withoutSelfLoops.edges
          simp only [IntegerProgram.withoutSelfLoops, List.mem_filter, bne_iff_ne]
          exact ⟨h_edge, hsl⟩) (skeletonProject p)

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



/-- Re-index the start location of a semantic path along an equality of locations
    (the env and end location are untouched). -/
def SemanticPath.castStart {ip : IntegerProgram} {env : Env} {u u' v : Nat}
    (h : u = u') (p : SemanticPath ip env u v) : SemanticPath ip env u' v := h ▸ p

@[simp] lemma SemanticPath.castStart_length {ip : IntegerProgram} {env : Env}
    {u u' v : Nat} (h : u = u') (p : SemanticPath ip env u v) :
    (SemanticPath.castStart h p).length = p.length := by
  subst h; rfl

@[simp] lemma SemanticPath.castStart_skeletonSteps {ip : IntegerProgram} {env : Env}
    {u u' v : Nat} (h : u = u') (p : SemanticPath ip env u v) :
    (SemanticPath.castStart h p).skeletonSteps = p.skeletonSteps := by
  subst h; rfl

/-- A semantic path of `ip` that `usesOnly t` is, step for step, a semantic path
    of the single-transition program `transition_to_ip t`: convert it to one of
    the same length. (`t` is a self-loop, so every location on the run is `t.src`.) -/
private lemma usesOnly_toSingle
    {ip : IntegerProgram} {t : Transition}
    (h_self : t.src = t.tgt) (h_edge : t ∈ ip.edges)
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    p.usesOnly t →
      ∃ q : SemanticPath (ip.transition_to_ip t h_self h_edge) env t.src t.src,
        q.length = p.length := by
  induction p with
  | nil u env h =>
      intro _
      exact ⟨.nil t.src env (by simp [IntegerProgram.transition_to_ip]), rfl⟩
  | cons env t' h_edge' hguard env' hupdate p' ih =>
      intro huses
      -- usesOnly on a cons unfolds to: this step is `t`, and the tail uses only `t`.
      simp only [SemanticPath.usesOnly] at huses
      obtain ⟨ht', hp'⟩ := huses
      subst ht'
      obtain ⟨q, hq⟩ := ih hp'
      -- Prepend the step `t'` in `transition_to_ip`; the tail starts at `t'.tgt = t'.src`.
      refine ⟨.cons env t' (by simp [IntegerProgram.transition_to_ip]) hguard env' hupdate
                (SemanticPath.castStart h_self q), ?_⟩
      simp only [SemanticPath.length, SemanticPath.castStart_length, hq]

/-- A self-loop transition `t` with a Farkas witness admits a uniform length
    bound `N` on every run of `ip` from `env` that uses only `t`. The witness makes
    `transition_to_ip t` terminate (`termination_of_farkas_witness`); a `usesOnly t`
    run embeds into that program with the same length, so its bound transfers. -/
lemma selfloop_run_bounded
    {ip : IntegerProgram} {t : Transition}
    (h_self : t.src = t.tgt) (h_edge : t ∈ ip.edges)
    {n m : ℕ} (w : LASW.FarkasWitness n m)
    (h_repr : w.RepresentsProgram (ip.transition_to_ip t h_self h_edge))
    (env : Env) :
    ∃ N : Nat, ∀ {u v : Nat} (p : SemanticPath ip env u v),
      SemanticPath.usesOnly t p → p.length ≤ N := by
  obtain ⟨N, hN⟩ := (LASW.termination_of_farkas_witness w h_repr) env
  refine ⟨N, ?_⟩
  intro u v p huses
  obtain ⟨q, hq⟩ := usesOnly_toSingle h_self h_edge p huses
  rw [← hq]
  exact hN q

/-- A `usesLoopsAt l` run of `ip` is, step for step, a semantic path of the
    sub-program `selfloops_to_ip l`: convert it to one of the same length. -/
private lemma usesLoopsAt_toSub
    {ip : IntegerProgram} {l : Nat}
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    p.usesLoopsAt l →
      ∃ q : SemanticPath (ip.selfloops_to_ip l) env l l, q.length = p.length := by
  induction p with
  | nil u env h =>
      intro _
      exact ⟨.nil l env (by simp [IntegerProgram.selfloops_to_ip]), rfl⟩
  | cons env t h_edge hguard env' hupdate p' ih =>
      intro huses
      simp only [SemanticPath.usesLoopsAt] at huses
      obtain ⟨hsrc, htgt, hp'⟩ := huses
      obtain ⟨q, hq⟩ := ih hp'
      have hmem : t ∈ (ip.selfloops_to_ip l).edges :=
        IntegerProgram.mem_selfloops_to_ip_edges.mpr ⟨h_edge, hsrc, htgt⟩
      -- Prepend the step `t`; re-index its endpoints (`t.src = t.tgt = l`).
      refine ⟨SemanticPath.castStart hsrc
                (.cons env t hmem hguard env' hupdate
                  (SemanticPath.castStart htgt.symm q)), ?_⟩
      simp only [SemanticPath.castStart_length, SemanticPath.length, hq]

/-- The self-loops at a location `l` with a (single, joint) Farkas witness admit a
    uniform length bound `N` on every run of `ip` from `env` that stays at `l`. The
    witness makes `selfloops_to_ip l` terminate; a `usesLoopsAt l` run embeds into
    that program with the same length, so its bound transfers. -/
lemma selfloops_run_bounded
    {ip : IntegerProgram} {l : Nat}
    {n m : ℕ} (w : LASW.FarkasWitness n m)
    (h_repr : w.RepresentsProgram (ip.selfloops_to_ip l))
    (env : Env) :
    ∃ N : Nat, ∀ {u v : Nat} (p : SemanticPath ip env u v),
      SemanticPath.usesLoopsAt l p → p.length ≤ N := by
  obtain ⟨N, hN⟩ := (LASW.termination_of_farkas_witness w h_repr) env
  refine ⟨N, ?_⟩
  intro u v p huses
  obtain ⟨q, hq⟩ := usesLoopsAt_toSub p huses
  rw [← hq]
  exact hN q

/-! ### Uniform bound via well-founded recursion on the step relation

Configurations are `(state, location)` pairs; one semantic step is `StepRel`.
Because each location's self-loops jointly terminate and the skeleton is acyclic,
the program has no infinite run — i.e. `StepRel` is well-founded (`stepRel_wf`).
Well-founded recursion over it produces, for every start configuration, a uniform
bound on path length (`config_length_bounded`); the self-loop count is part of the
length, giving `total_selfloop_steps_bounded`. -/

/-- A configuration of a run: a state together with the current location. -/
abbrev Config := Env × Nat

/-- `PathLenBounded ip e u B`: every semantic path from state `e` at location `u`
    has length at most `B`. Monotone in `B`. -/
def PathLenBounded (ip : IntegerProgram) (e : Env) (u : Nat) (B : Nat) : Prop :=
  ∀ {v : Nat} (p : SemanticPath ip e u v), p.length ≤ B

lemma PathLenBounded.mono {ip : IntegerProgram} {e : Env} {u : Nat} {b b' : Nat}
    (h : b ≤ b') (hP : PathLenBounded ip e u b) : PathLenBounded ip e u b' := by
  intro v p; exact le_trans (hP p) h

/-- One semantic step between configurations: some enabled edge from `c` to `c'`. -/
def StepRel (ip : IntegerProgram) (c' c : Config) : Prop :=
  ∃ t ∈ ip.edges, t.src = c.2 ∧ t.perform c.1 = some c'.1 ∧ t.tgt = c'.2

/-- The finite list of one-step successors of a configuration. -/
def succs (ip : IntegerProgram) (c : Config) : List Config :=
  ip.edges.filterMap (fun t =>
    if t.src = c.2 then (t.perform c.1).map (fun e' => (e', t.tgt)) else none)

lemma mem_succs {ip : IntegerProgram} {c c' : Config} :
    c' ∈ succs ip c ↔ StepRel ip c' c := by
  obtain ⟨e', u'⟩ := c'
  obtain ⟨e, u⟩ := c
  simp only [succs, StepRel, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, hc⟩
    by_cases hsrc : t.src = u
    · rw [if_pos hsrc, Option.map_eq_some_iff] at hc
      obtain ⟨w, hperf, hw⟩ := hc
      simp only [Prod.mk.injEq] at hw
      obtain ⟨rfl, rfl⟩ := hw
      exact ⟨t, ht, hsrc, hperf, rfl⟩
    · rw [if_neg hsrc] at hc; exact absurd hc (by simp)
  · rintro ⟨t, ht, hsrc, hperf, htgt⟩
    exact ⟨t, ht, by rw [if_pos hsrc, hperf, Option.map_some, htgt]⟩

/-- A path with no skeleton steps stays at its start location. -/
private lemma skeletonSteps_zero_usesLoopsAt {ip : IntegerProgram}
    {e : Env} {u v : Nat} (p : SemanticPath ip e u v) :
    p.skeletonSteps = 0 → p.usesLoopsAt u := by
  induction p with
  | nil u e h => intro _; exact trivial
  | cons e t h_edge hguard e' hupdate p' ih =>
      intro hk
      simp only [SemanticPath.skeletonSteps] at hk
      have hsl : t.src = t.tgt := by
        by_contra h; rw [if_neg h] at hk; omega
      rw [if_pos hsl, Nat.zero_add] at hk
      refine ⟨rfl, hsl.symm, ?_⟩
      rw [hsl]; exact ih hk

/-- From `t.perform e = some e'` recover the guard and update facts of the step. -/
private lemma perform_eq_some {t : Transition} {e e' : Env}
    (h : t.perform e = some e') :
    Constraint.eval t.guard e = some true ∧ Update.all t.update e = some e' := by
  unfold Transition.perform at h
  cases hg : Constraint.eval t.guard e with
  | none => simp [hg] at h
  | some b =>
      cases b with
      | false => simp [hg] at h
      | true => simp [hg] at h; exact ⟨rfl, h⟩

/-- Number of skeleton steps among run-steps `i, …, i+N-1` of a transition stream. -/
def runSkelCount (t : ℕ → Transition) (i : Nat) : Nat → Nat
  | 0     => 0
  | N + 1 => (if (t i).src = (t i).tgt then 0 else 1) + runSkelCount t (i + 1) N

lemma runSkelCount_succ (t : ℕ → Transition) (i N : Nat) :
    runSkelCount t i (N + 1)
      = runSkelCount t i N + (if (t (i + N)).src = (t (i + N)).tgt then 0 else 1) := by
  induction N generalizing i with
  | zero => simp [runSkelCount]
  | succ N ih =>
      rw [runSkelCount, ih (i + 1), runSkelCount]
      have h : (i + 1) + N = i + (N + 1) := by omega
      rw [h]; ring

private lemma runSkelCount_eq_zero (t : ℕ → Transition) (i N : Nat)
    (hall : ∀ k, i ≤ k → (t k).src = (t k).tgt) : runSkelCount t i N = 0 := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
      rw [runSkelCount, if_pos (hall i (le_refl i)),
        ih (i + 1) (fun k hk => hall k (Nat.le_of_succ_le hk))]

/-- From an infinite run (a transition stream matching a config stream `f`), a
    semantic path of any length `N` starting at `f i`, whose skeleton-step count is
    exactly `runSkelCount t i N`. -/
private lemma run_prefix_path {ip : IntegerProgram} (f : ℕ → Env × Nat) (t : ℕ → Transition)
    (ht : ∀ n, t n ∈ ip.edges)
    (hsrc : ∀ n, (t n).src = (f n).2)
    (hg : ∀ n, Constraint.eval (t n).guard (f n).1 = some true)
    (hu : ∀ n, Update.all (t n).update (f n).1 = some (f (n + 1)).1)
    (htgt : ∀ n, (t n).tgt = (f (n + 1)).2) :
    ∀ (i N : Nat), ∃ (w : Nat) (p : SemanticPath ip (f i).1 (f i).2 w),
      p.length = N ∧ p.skeletonSteps = runSkelCount t i N := by
  intro i N
  induction N generalizing i with
  | zero =>
      have hmem : (f i).2 ∈ ip.locs := by
        have := (ip.h_edges (t i) (ht i)).1; rwa [hsrc i] at this
      exact ⟨(f i).2, .nil (f i).2 (f i).1 hmem, rfl, rfl⟩
  | succ N ih =>
      obtain ⟨w', p', hlen', hskel'⟩ := ih (i + 1)
      refine ⟨w', SemanticPath.castStart (hsrc i)
        (.cons (f i).1 (t i) (ht i) (hg i) (f (i + 1)).1 (hu i)
          (SemanticPath.castStart (htgt i).symm p')), ?_, ?_⟩
      · simp only [SemanticPath.castStart_length, SemanticPath.length, hlen']; omega
      · simp only [SemanticPath.castStart_skeletonSteps, SemanticPath.skeletonSteps, hskel',
          runSkelCount]

/-- A monotone, bounded sequence of naturals is eventually constant. -/
private lemma exists_eventually_const {c : ℕ → ℕ} {B : ℕ}
    (hmono : Monotone c) (hbd : ∀ N, c N ≤ B) : ∃ M, ∀ N, M ≤ N → c N = c M := by
  have hne : (Set.range c).Nonempty := ⟨c 0, 0, rfl⟩
  have hbdd : BddAbove (Set.range c) := ⟨B, by rintro _ ⟨N, rfl⟩; exact hbd N⟩
  obtain ⟨M, hM⟩ := Nat.sSup_mem hne hbdd
  refine ⟨M, fun N hN => ?_⟩
  have h1 : c M ≤ c N := hmono hN
  have h2 : c N ≤ c M := by rw [hM]; exact le_csSup hbdd ⟨N, rfl⟩
  omega

/-- The step relation is well-founded: the program has no infinite run. This is the
    one remaining leaf obligation of the termination proof; it packs the two
    ingredients — each location's self-loops jointly terminate (`h_witnesses`) and
    the skeleton is acyclic (`h_upto`).

    Intended proof (classical, via `wellFounded_iff_isEmpty_descending_chain`):
    an infinite run `f : ℕ → Config` with `StepRel (f (n+1)) (f n)` would, for each
    `N`, give a semantic path from `f 0` of length `N`; by `skeleton_steps_bounded`
    its skeleton-step count is `≤ locs.length`. That count is monotone in `N` and
    bounded, hence eventually constant, so beyond some `M` every step is a self-loop
    at one fixed location `l`. The tail is then an unbounded self-loop run at `l`,
    contradicting termination of `selfloops_to_ip l` (`selfloops_run_bounded`). -/
lemma stepRel_wf (ip : IntegerProgram)
    (h_witnesses : ∀ l ∈ ip.locs,
        ∃ (n m : ℕ) (w : LASW.FarkasWitness n m),
          w.RepresentsProgram (ip.selfloops_to_ip l))
    (h_upto : ip.AcyclicUpToSelfLoops) :
    WellFounded (StepRel ip) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun hchain => ?_⟩
  obtain ⟨f, hf⟩ := hchain
  simp only [StepRel] at hf
  -- Extract, for each step `n`, the transition `t n` used and its facts.
  choose t htmem hsrc hperf htgt using hf
  have hg : ∀ n, Constraint.eval (t n).guard (f n).1 = some true :=
    fun n => (perform_eq_some (hperf n)).1
  have hu : ∀ n, Update.all (t n).update (f n).1 = some (f (n + 1)).1 :=
    fun n => (perform_eq_some (hperf n)).2
  -- Skeleton-step count of the length-`N` prefix is `≤ locs.length`.
  have hcount_bd : ∀ N, runSkelCount t 0 N ≤ ip.locs.length := by
    intro N
    obtain ⟨w, p, _, hskel⟩ := run_prefix_path f t htmem hsrc hg hu htgt 0 N
    have := skeleton_steps_bounded h_upto p
    rwa [hskel] at this
  -- Monotone and bounded ⟹ eventually constant ⟹ eventually only self-loops.
  have hmono : Monotone (runSkelCount t 0) :=
    monotone_nat_of_le_succ (fun N => by rw [runSkelCount_succ]; exact Nat.le_add_right _ _)
  obtain ⟨M, hM⟩ := exists_eventually_const hmono hcount_bd
  have hself : ∀ n, M ≤ n → (t n).src = (t n).tgt := by
    intro n hn
    have h1 : runSkelCount t 0 (n + 1) = runSkelCount t 0 n := by
      rw [hM (n + 1) (by omega), hM n hn]
    rw [runSkelCount_succ, Nat.zero_add] at h1
    by_contra hne
    rw [if_neg hne] at h1
    omega
  -- Hence the location is fixed after `M`.
  have hloc : ∀ n, M ≤ n → (f n).2 = (f M).2 := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ k hk ih => rw [← htgt k, ← hself k hk, hsrc k, ih]
  -- Build an arbitrarily long self-loop run at `l := (f M).2` and contradict its bound.
  set l := (f M).2 with hl
  have hl_mem : l ∈ ip.locs := by
    have := (ip.h_edges (t M) (htmem M)).1; rwa [hsrc M] at this
  obtain ⟨n, m, w, h_repr⟩ := h_witnesses l hl_mem
  obtain ⟨K, hK⟩ := selfloops_run_bounded w h_repr (f M).1
  obtain ⟨wpath, p, hlen, hskel⟩ := run_prefix_path f t htmem hsrc hg hu htgt M (K + 1)
  rw [runSkelCount_eq_zero t M (K + 1) (fun k hk => hself k hk)] at hskel
  have hle := hK p (skeletonSteps_zero_usesLoopsAt p hskel)
  rw [hlen] at hle
  omega

/-- The start location of any semantic path is a location of the program. -/
lemma pathStart_mem {ip : IntegerProgram} {e : Env} {u v : Nat}
    (p : SemanticPath ip e u v) : u ∈ ip.locs := by
  cases p with
  | nil u e h => exact h
  | cons e t h_edge hguard e' hupdate p' => exact (ip.h_edges t h_edge).1

private lemma le_foldr_max (l : List Nat) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => intro x hx; simp at hx
  | cons a t ih =>
      intro x hx
      rw [List.foldr_cons]
      rcases List.mem_cons.mp hx with h | h
      · subst h; exact le_max_left _ _
      · exact le_trans (ih x h) (le_max_right _ _)

/-- Turn a per-element bound (`∀ a ∈ l, ∃ B, P a B`) into a single uniform bound,
    for a `B`-monotone predicate `P` over a finite list. -/
private lemma finite_choice_max {α : Type*} (l : List α) (P : α → Nat → Prop)
    (hmono : ∀ a {b b' : Nat}, b ≤ b' → P a b → P a b')
    (h : ∀ a ∈ l, ∃ b, P a b) : ∃ B, ∀ a ∈ l, P a B := by
  classical
  refine ⟨(l.attach.map (fun a => Classical.choose (h a.1 a.2))).foldr max 0, ?_⟩
  intro a ha
  refine hmono a ?_ (Classical.choose_spec (h a ha))
  apply le_foldr_max
  exact List.mem_map.mpr ⟨⟨a, ha⟩, List.mem_attach _ _, rfl⟩

/-- Well-founded recursion on `StepRel`: from any configuration, path length is
    uniformly bounded. -/
lemma config_length_bounded {ip : IntegerProgram} (hwf : WellFounded (StepRel ip))
    (c0 : Config) : ∃ B, PathLenBounded ip c0.1 c0.2 B := by
  refine WellFounded.induction (C := fun c => ∃ B, PathLenBounded ip c.1 c.2 B) hwf c0 ?_
  clear c0
  rintro ⟨e, u⟩ IH
  -- Bound the successors uniformly using the induction hypothesis.
  obtain ⟨B0, hB0⟩ := finite_choice_max (succs ip (e, u))
    (fun c' B => PathLenBounded ip c'.1 c'.2 B)
    (fun c' => PathLenBounded.mono)
    (fun c' hc' => IH c' (mem_succs.mp hc'))
  refine ⟨B0 + 1, ?_⟩
  intro v p
  cases p with
  | nil u e h => simp [SemanticPath.length]
  | cons e t h_edge hguard e' hupdate p' =>
      have hstep : StepRel ip (e', t.tgt) (e, t.src) :=
        ⟨t, h_edge, rfl, by simp [Transition.perform, hguard, hupdate], rfl⟩
      have hb : p'.length ≤ B0 := hB0 (e', t.tgt) (mem_succs.mpr hstep) p'
      simp only [SemanticPath.length]
      omega

/-- **The self-loop budget.** Every run from `env` performs at most `B` self-loop
    steps in total, provided each location's *joint* self-loop program has a Farkas
    witness (`h_witnesses`) and the skeleton is acyclic (`h_upto`).

    Soundness note: the hypothesis is stated *per location* — a single witness for
    `selfloops_to_ip l` covering **all** self-loops at `l` — not per individual
    self-loop. That is essential: individual witnesses do not preclude two
    self-loops at one location from interleaving into a non-terminating run
    (`x'=x-1,y'=y+1` ∥ `x'=x+1,y'=y-1`). Under the corrected hypothesis no such
    joint witness exists, so the statement is sound.

    Proof: `stepRel_wf` gives well-foundedness of the one-step relation on
    configurations `(state, location)`. `config_length_bounded` turns that into a
    uniform path-length bound from every start configuration by well-founded
    recursion (finite branching over `ip.edges` handled by a `foldl max`), and the
    self-loop count is bounded by the length. The only remaining leaf obligation is
    `stepRel_wf` itself ("the program has no infinite run"). -/
lemma total_selfloop_steps_bounded
    {ip : IntegerProgram}
    (h_witnesses : ∀ l ∈ ip.locs,
        ∃ (n m : ℕ) (w : LASW.FarkasWitness n m),
          w.RepresentsProgram (ip.selfloops_to_ip l))
    (h_upto : ip.AcyclicUpToSelfLoops)
    (env : Env) :
    ∃ B : Nat, ∀ {u v : Nat} (p : SemanticPath ip env u v), p.selfLoopSteps ≤ B := by
  have hwf := stepRel_wf ip h_witnesses h_upto
  -- Uniformly bound path length over every start location `u ∈ locs`.
  obtain ⟨B, hB⟩ := finite_choice_max ip.locs (fun u B => PathLenBounded ip env u B)
    (fun u => PathLenBounded.mono)
    (fun u _ => config_length_bounded hwf (env, u))
  refine ⟨B, ?_⟩
  intro u v p
  have hlen : p.length ≤ B := hB u (pathStart_mem p) p
  have hsl : p.selfLoopSteps ≤ p.length := by
    rw [length_eq_selfloop_add_skeleton]; omega
  omega

-- main theorem
theorem terminates_of_selfloops_rank
    {ip : IntegerProgram}
    (h_witnesses : ∀ l ∈ ip.locs,
        ∃ (n m : ℕ) (w : LASW.FarkasWitness n m),
          w.RepresentsProgram (ip.selfloops_to_ip l))
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
  simp only [IntegerProgram.withoutSelfLoops,List.mem_filter] at ht
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
