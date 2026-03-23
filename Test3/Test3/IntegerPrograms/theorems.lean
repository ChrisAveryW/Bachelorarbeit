import Test3.IntegerPrograms.IntegerPrograms
import Test3


open IntegerProgram


-- some lemma to prove that acyclic integer programs are have finite rc(σ) for any σ.


-- lemma to prove that a configuration step perserves the corresponding integer program
lemma c_step_preserves_prog (c1 c2 : Configuration)
  (h : Configuration.step c1 c2) : c1.prog = c2.prog := by
  rw[Configuration.step] at h
  cases h with
  | intro h1 h2 =>
    exact h1

-- Since we argue about acyclicity, which is a property of graphs, it is important to show that
-- configuration step corresponds to a transition
lemma step_gives_syntactic_edge (c1 c2 : Configuration)
  (h : Configuration.step c1 c2) :
  ∃ t ∈ c1.prog.edges, t.src = c1.loc ∧ t.tgt = c2.loc := by
  unfold Configuration.step at h
  have hprog : c1.prog = c2.prog := c_step_preserves_prog c1 c2 h
  obtain ⟨_, ht, ht_edge, _, _, ht_tgt⟩ := h
  exact ⟨ht, ht_edge, ht_tgt⟩

-- Lemma to show that a path of length one is equal to a step
-- Remark: new definition of pathN would change this lemma
lemma step_gives_pathN_one (c1 c2 : Configuration)
  (h : Configuration.step c1 c2) :
  IntegerProgram.pathN 1 c1.loc c2.loc c1.prog := by
  unfold IntegerProgram.pathN
  unfold Configuration.step at h
  obtain ⟨_, ht, ht_edge, _, _, ht_src, ht_tgt⟩ := h
  left
  exact ⟨ht, ht_edge, ht_src, ht_tgt⟩

-- Lemma that entirely shows that paths on a configuration-level behave the same as on graph-level
-- acyclicity is a graph property. However rc is a configuration property, thus we need to their implication.
lemma semantic_implies_syntactic
    (n : ℕ) (c1 c2 : Configuration)
    (h_path : Configuration.pathN n c1 c2) :
    IntegerProgram.pathN n c1.loc c2.loc c1.prog := by
    induction n generalizing c1 with
    | zero  => exact absurd h_path (by simp [Configuration.pathN])
    | succ k ih =>
      unfold Configuration.pathN at h_path
      unfold IntegerProgram.pathN
      cases h_path with
      | inl h_step =>
        unfold Configuration.step at h_step
        obtain ⟨t, ht_edge, _, _, ht_src, ht_tgt⟩ := h_step.2
        left
        exact ⟨t, ht_edge, ht_src, ht_tgt⟩
      | inr h_mid =>
        right
        unfold Configuration.step at h_mid
        obtain ⟨ci, h_prog , h_in⟩ := h_mid
        obtain ⟨h_pref, h_ed⟩ := h_prog
        obtain ⟨h_edg, h_log⟩ := h_ed
        obtain ⟨h_set, h_con⟩ := h_log
        obtain ⟨_, h_la⟩ := h_con.2
        refine ⟨h_edg, ?_, ?_ , ?_ ⟩
        exact h_set
        exact h_la.left
        rw[h_la.2, h_pref]
        exact ih ci h_in

-- This lemma might not be needed.
-- It should provide a list of locations that were seen.
lemma pathN_to_loc_list (n l1 l2 : ℕ) (p : IntegerProgram)
    (h : IntegerProgram.pathN n l1 l2 p) :
    ∃ locs : List ℕ, locs.length = n + 1 ∧
    ∀ l ∈ locs, l ∈ p.locs := by
    sorry


-- This lemma proves that if the supremum of a set equals infinity, this set is unbounded
-- meaning it has arbitrary high natural numbers
lemma ssup_eq_top_unbounded (S : Set ℕ∞) (h : sSup S = ⊤) :
  ∀ M : ℕ, ∃ k ∈ S, (M : ℕ∞) < k := by
  intro M
  by_contra h_bound
  push_neg at h_bound
  have : sSup S ≤ (M : ℕ∞) := sSup_le h_bound
  simp [h] at this

-- Lemma: shows that if we have a long path (a path that is longer than the number of locations)
-- then there are locations that were revisited
-- TODO: prove through pigeonhole principle (Mathlib could help). Unfortunately haven't solved this yet.
lemma long_path_has_cycle
    (p : IntegerProgram) (n : ℕ) (l1 l2 : ℕ)
    (h_long : n > p.locs.length)
    (h_path : IntegerProgram.pathN n l1 l2 p) :
    ∃ l ∈ p.locs, IntegerProgram.path l l p := by
    sorry

def IntegerProgram.has_transition (p : IntegerProgram) (a b : ℕ) : Prop :=
  ∃ t : Transition, t ∈ p.edges ∧ t.src = a ∧ t.tgt = b


-- lemma: shows that a step perserves the integer program locations-set.
-- Remark: this could be helpful for proving the long_path_has_cycle lemma, since this is a crucial part the proof.
lemma step_only_visits_ip_locs
  (p : IntegerProgram)
  (a b : ℕ) : IntegerProgram.has_transition p a b → a ∈ p.locs ∧ b ∈ p.locs := by
    unfold IntegerProgram.has_transition
    intro h_ed
    rcases h_ed with ⟨t', ⟨h_mem, h_src, h_tgt⟩⟩
    have h1 := p.h_trans t' h_mem
    rw[← h_src, ← h_tgt]
    exact h1

-- lemma: shows that a path perserves the integer program locations-set.
-- This is the next step of the lemma step_only_visits_ip_locs
-- Todo: unfortunately, haven't solved how I can prove this.
lemma path_only_visits_ip_locs
  (p : IntegerProgram)
  (a b : ℕ) : IntegerProgram.path a b p:= by
  sorry

-- lemma: that shows that acyclic graphs won't have repeated locations
-- Remarks: this might make the prove of path_only_visits_ip_locs unnecessary.
lemma acyclic_impl_no_repeated_locs
  (p : IntegerProgram)
  (h : IntegerProgram.acyclic p) :
  ∀ (n ls lt : ℕ), IntegerProgram.pathN n ls lt p → ls ≠ lt := by
  intro n ls lt pa h_eq
  subst h_eq
  have hp : IntegerProgram.path ls ls p := ⟨n, pa⟩
  have hmem : ls ∈ p.locs := by
    cases n with
    | zero => simp [IntegerProgram.pathN] at pa
    | succ n =>
      simp [IntegerProgram.pathN] at pa
      rcases pa with ⟨t, ht_mem, ht_src, _⟩ | ⟨t, ht_mem, ht_src, _⟩
      · rw [← ht_src]
        exact (p.h_trans t ht_mem).left
      · rw [← ht_src]
        exact (p.h_trans t ht_mem).left
  exact h ls hmem hp


-- Main Theorem: acyclic graphs imply that for arbitrary start configurations, any run will be finite.
-- TODO: unfortunately not enough lemma to prove this efficiently.
theorem acyclic_impl_finite_rc
    (p : IntegerProgram)
    (c : Configuration)
    (h_in: c.loc = p.l₀) -- wir fangen in der Startposition an
    (h_ac: IntegerProgram.acyclic p) -- Integerprogram ist azyklisch
    (h_tr: ∃ n : ℕ, n = p.edges.length) -- endliche kanten
    (h_lo: ∃ n : ℕ, n = p.locs.length) : -- endliche knoten
    Configuration.rc c ≠ ⊤ := by
    intro cont
    unfold Configuration.rc at cont
    unfold Configuration.all_succ_lengths at cont
    unfold IntegerProgram.acyclic at h_ac
    sorry
