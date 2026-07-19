import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Basic
import leantermination.Datastructures.IntegerProgram
import Mathlib.Algebra.Polynomial.Basic

set_option linter.style.longLine false


/-!
Lemmas and theorems to show the resulting theorem `Acyclic_impl_Termination`.
-/

/--
This lemma shows that the function `SemanticPath.toSyntactic` preserves length.
It works by induction over the two cases of a SemanticPath.
-/
lemma SemanticPath.toSyntactic_length {ip : IntegerProgram} {env : Env} {u v : Nat}
    (p : SemanticPath ip env u v) : p.toSyntactic.length = p.length := by
  induction p with
  | nil _ _ _           => rfl
  | cons _ _ _ _ _ _ _ ih =>
      simp only [SemanticPath.toSyntactic, SyntacticPath.length, SemanticPath.length, ih]

/--
This lemma just changes the interaction of the `SemanticPath.toSyntatctic_length` lemma.
It doesn't introduce any new knowledge, is more of making this lemma more convenient.
-/
lemma SemanticPath.synatactic_length {ip : IntegerProgram} {env : Env} {u v : Nat}
    (p : SemanticPath ip env u v)
    (p' : SyntacticPath ip u v)
    (h_eq : p.toSyntactic = p') :
    p'.length = p.length := by
  rw [← h_eq]
  rw [SemanticPath.toSyntactic_length]

/--
This lemma proves that the length of `SyntacticPath` stands in a specific relation to the length
of visited locations. The number of visited locations is always one more than the path length.
This is because the path length is defined on the number of transitions.
-/
lemma SyntacticPath.visited_length {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : p.visited.length = p.length + 1 := by
  induction p with
  | nil _ _       => simp only [visited, List.length_cons, List.length_nil, zero_add, length]
  | cons _ _ _ ih =>
    simp only [visited, List.length_cons, ih, length, Nat.add_right_cancel_iff]
    omega

/--
This lemma generalizes the `IntegerProgram.h_egdes` invariant to a paths visited locations.
It works by going inductivley going through the construction of a path.
-/
lemma SyntacticPath.visited_mem {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : ∀ x ∈ p.visited, x ∈ ip.locs := by
  induction p with
  | nil u hu =>
      intro x hx
      simp only [visited, List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      exact hu
  | cons t ht _ ih =>
      intro x hx
      simp only [SyntacticPath.visited, List.mem_cons] at hx
      cases hx with
        | inl heq =>
          subst heq
          exact (ip.h_edges t ht).1
        | inr hx =>
          exact ih x hx


/--
This lemma serves as proof helper. It allows other proofs to obtain a (propositional) `SyntacticPath`
which starts in the same location as the provided path and ends in some location which which is in the among the visited locations.
-/
lemma SyntacticPath.visited_subpath {ip : IntegerProgram} {u v : Nat}
    (p : SyntacticPath ip u v) : ∀ x ∈ p.visited, Nonempty (SyntacticPath ip u x) := by
  induction p with
  | nil u hu =>
      intro x hx
      simp only [SyntacticPath.visited, List.mem_singleton] at hx
      rw [hx]
      exact ⟨.nil u hu⟩
  | cons t ht q ih =>
      intro x hx
      simp only [SyntacticPath.visited, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨.nil t.src (ip.h_edges t ht).1⟩
      · obtain ⟨p'⟩ := ih x hx
        exact ⟨.cons t ht p'⟩


/- adr
This is one important milestone in the proof of Acyclicty → Termination.
Therefore this section will be verbose.

This lemma, shows that visited nodes of a `SyntacticPath` are unique, thus a non-duplicate list.
Proof step by step:
The proof deconstructs the constructors of `SyntacticPath` by induction.
- The base-case is solved simply by the Std-Theorem, which says that singletons are non-duplicate
(which they obiously are).
- The recursive-case is solved through a contradiction:
We can express the recursive case as
t.src ∉ q.visited ∧ q.visited is non-duplicate. So splitting the the head and tail of the list parts
The second part of the konjunction can be solved by the induction hypothesis.
The first part has to be proven: for this we assume that t.src ∈ q.visited to create a contradiction
Since this t.src ∈ q.visited there exists a path: SyntactcPath ip t.tgt t.src := p
If we create the successor: SyntacticPath.cons t _ p => we receive SyntacticPath t.src t.src
Since we created it with SyntacticPath.cons the length is at least ≥ 1, which contradicts t.src ∈ q.visited

So in short, if we added a new transition t, then we can conclude that if it were source location
was already in the path, then (since we add the transition with cons) there would be a real self loop from
t.src to t.src resulting in the contradiction that it is acyclic!
-/
lemma SyntacticPath.visited_nodup {ip : IntegerProgram}
    (h_acyc : IntegerProgram.Acyclic ip) {u v : Nat}
    (p : SyntacticPath ip u v) : p.visited.Nodup := by
  induction p with
  | nil u' _ => exact List.nodup_singleton u'
  | cons t ht q ih =>
      rw [SyntacticPath.visited, List.nodup_cons]
      refine ⟨?_, ih⟩
      intro hmem
      obtain ⟨p'⟩ := q.visited_subpath _ hmem
      have hcycle : (.cons t ht p' : SyntacticPath ip t.src t.src).length = 0 := h_acyc _
      simp only [SyntacticPath.length] at hcycle
      omega

/- adr
This lemma has two assumptions: it assumes a non-duplicate list and a subset/sublist relationship between the non-duplicate list and another reference list.
Since the list is non-duplicate it can be seen as a finite set. This finite set can be seen as a subset to the reference list (which can have duplicates).
Thus the non-duplicate subset/list has less-than or equal number of elements.
-/

/--
This lemma is the calculation part of the proof Acyclic → Termination.
It inferes from a non-duplicate list, that the length must be lessthan or equal to which it is a subset.
-/
lemma nodup_sublist_length {α : Type*} {l ref : List α}
    (h_nd : l.Nodup) (h_sub : ∀ x ∈ l, x ∈ ref) : l.length ≤ ref.length := by
  classical
  have h1 : l.length = l.toFinset.card := (List.toFinset_card_of_nodup h_nd).symm
  have h2 : l.toFinset ⊆ ref.toFinset := by
    intro x hx
    simp only [List.mem_toFinset] at *
    exact h_sub x hx
  exact calc l.length = l.toFinset.card   := h1
    _                 ≤ ref.toFinset.card := Finset.card_le_card h2
    _                 ≤ ref.length        := List.toFinset_card_le ref

/--
This theorem shows that acyclic `IntegerPrograms` are bound in their path length.
It works by showing that paths of acyclic integer programs have non-duplicat visited locations,
which are all out of the location universe of an integer program.
Therefore we can use the lemma that shows the length of the visited locations is smaller or equal to the size of our location universe.
Then we rewrite this result path length (from the visited locations size).
-/
theorem acyclic_impl_bounded_SyntacticPath
    {ip : IntegerProgram} {u v : Nat}
    (h_acyc : IntegerProgram.Acyclic ip)
    (p : SyntacticPath ip u v) :
    p.length < ip.locs.length := by
  have h_nodup  := SyntacticPath.visited_nodup h_acyc p
  have h_mem := SyntacticPath.visited_mem p
  have h_le  := nodup_sublist_length h_nodup h_mem
  rw [SyntacticPath.visited_length] at h_le
  omega


/--
This lemma generalizes `acyclic_impl_bound_SyntacticPath` to show that all acyclic integer programs have bound paths, thus terminate.
-/
theorem Acyclic_impl_Termination (ip : IntegerProgram) :
    IntegerProgram.Acyclic ip → IntegerProgram.Termination ip := by
  intro h_acyc
  unfold IntegerProgram.Termination
  intro e
  use ip.locs.length
  intro u v p
  let syntactic_path := p.toSyntactic -- introduced to make it more clear, could be collapsed
  have h_eq : p.toSyntactic = syntactic_path := rfl
  have h1 := acyclic_impl_bounded_SyntacticPath h_acyc syntactic_path
  rw [SemanticPath.synatactic_length p syntactic_path h_eq] at h1
  omega
