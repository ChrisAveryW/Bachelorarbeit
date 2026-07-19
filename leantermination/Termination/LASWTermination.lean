import leantermination.Datastructures.IntegerProgram
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Ring.Defs

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/-!
Following the paper "A Complete Method for the Synthesis of Linear Ranking Functions".
The main lemma `termination_of_farkas_witness` will be shown.
-/

namespace LASW

/--
This is the structure of the paper "A Complete Method for the Synthesis of Linear Ranking Functions".

`n` is the number of program variables
`m` is the number of inequalities in the matrix encoding (A A')(x,x') ≤ b
`A`, `A'` are m × n matrices over ℚ
`b : Fin m → ℚ` is the right-hand side vector
`lambda₁`, `lambda₂` are the nonnegative vectors

`h_1a`, ..., `h_1d` are the conditions that need to hold inorder to ensure the representing integer program terminates.
-/
structure FarkasWitness (n m : ℕ) where
  A : Fin m → Fin n → ℚ
  A' : Fin m → Fin n → ℚ
  b  : Fin m → ℚ
  lambda₁ : Fin m → ℚ
  lambda₂ : Fin m → ℚ
  h_nonneg₁ : ∀ i, 0 ≤ lambda₁ i
  h_nonneg₂ : ∀ i, 0 ≤ lambda₂ i
  -- λ₁ · A' = 0
  h_1a : ∀ j : Fin n, ∑ i, lambda₁ i * A' i j = 0
  -- (λ₁ - λ₂) · A = 0
  h_1b : ∀ j : Fin n, ∑ i, (lambda₁ i - lambda₂ i) * A i j = 0
  -- λ₂ · (A + A') = 0
  h_1c : ∀ j : Fin n, ∑ i, lambda₂ i * (A i j + A' i j) = 0
  -- λ₂ · b < 0
  h_1d : ∑ i, lambda₂ i * b i < 0

namespace FarkasWitness

/- adr
This fixes a variable for future definitions, which are provided from the paper.
The functions are derived from the FarkasWitness, and formalized exactly like *Theorem 1* defines it in the paper.
-/
variable {n m : ℕ} (w : FarkasWitness n m)

/-- Coefficients of the linear ranking function:  r := λ₂ · A' -/
def r (j : Fin n) : ℚ := ∑ i, w.lambda₂ i * w.A' i j

/-- Lower bound constant: δ₀ := -(λ₁ · b) -/
def delta₀ : ℚ := -(∑ i, w.lambda₁ i * w.b i)

/-- Strict decrease amount: δ := -(λ₂ · b). Positivity closable directly by h_1d -/
def delta : ℚ := -(∑ i, w.lambda₂ i * w.b i)

/-- The lemma that shows the positivity of `FarkasWitness.delta` (so δ > 0).
It is proven directly through (1d).
-/
lemma delta_pos : 0 < w.delta := by
  unfold delta
  exact neg_pos.mpr w.h_1d

end FarkasWitness

/--
Converts an `Env` into a rational vector of length n.
Indices past the list default to 0, better than Option since this would bload the Option handeling.
And could be considered safe, since non-written values wouldn't have any other sensible default.
-/
def Env.toVec (n : ℕ) (env : Env) : Fin n → ℚ :=
  fun i =>
    match env.vars[i.val]? with
    | some z => (z : ℚ)
    | none   => 0

/--
This is a single semantic path step formalized as proposition.
It breaks down something equivalent to a semantic path into a smaller piece that you can work with.
This is important since in this case we reason more about single transitions than about longer paths!
-/
def SemanticStep (ip : IntegerProgram) (env env' : Env) : Prop :=
  ∃ t ∈ ip.edges,
    Constraint.eval t.guard env = some true ∧
    Update.all t.update env = some env'

/--
Encoding correctness for a single transition.
Whenever t performs a step from env to env', the matrix inequality (A A')(env, env')ᵀ ≤ b holds.
-/
def FarkasWitness.RepresentsTransition
    {n m : ℕ} (w : FarkasWitness n m) (t : Transition) : Prop :=
  ∀ env env' : Env,
    Constraint.eval t.guard env = some true →
    Update.all t.update env = some env' →
    ∀ i : Fin m,
      (∑ j, w.A i j * Env.toVec n env j) +
      (∑ j, w.A' i j * Env.toVec n env' j) ≤ w.b i

/--
This is the generalization of the statement `FarkasWitness.RepresentsTransition` to a complete integer program.
-/
def FarkasWitness.RepresentsProgram
    {n m : ℕ} (w : FarkasWitness n m) (ip : IntegerProgram) : Prop :=
  ∀ t ∈ ip.edges, w.RepresentsTransition t

/--
A single semantic step implies the matrix inequality.
-/
lemma step_implies_matrix
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    {env env' : Env} (h_step : SemanticStep ip env env') :
    ∀ i : Fin m,
      (∑ j, w.A i j * Env.toVec n env j) +
      (∑ j, w.A' i j * Env.toVec n env' j) ≤ w.b i := by
  obtain ⟨t, h_edge, hguard, hupdate⟩ := h_step
  have h_repr_t : w.RepresentsTransition t := h_repr t h_edge
  intro i
  exact h_repr_t env env' hguard hupdate i

/--
Dedicated helper/convenience lemma which defeats the purpose for having to show this in
`decrease_on_step` and `bounded_on_loop_state` seperatly.
-/
private lemma sum_sum_swap_mul [Fintype ι] [Fintype κ] [CommSemiring R]
    (lam : ι → R) (M : ι → κ → R) (x : κ → R) :
    (∑ i, ∑ j, lam i * (M i j * x j))
      = ∑ j, (∑ i, lam i * M i j) * x j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/--
This is the strict decrease lemma:
The linear function r·x strictly decreases by at least δ on every step.
Thus this statement is ultimately shown: r · env' ≤ r · env - δ
-/
lemma decrease_on_step
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    {env env' : Env} (h_step : SemanticStep ip env env') :
    (∑ j, w.r j * Env.toVec n env' j) ≤
    (∑ j, w.r j * Env.toVec n env j) - w.delta := by
  -- creates both the variable representation of the paper
  set x  : Fin n → ℚ := Env.toVec n env  with hx
  set x' : Fin n → ℚ := Env.toVec n env' with hx'
  -- unfold matrix representation
  have h_mat : ∀ i : Fin m,
      (∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j) ≤ w.b i :=
    step_implies_matrix h_repr h_step
  -- Multiply row i by λ₂(i) ≥ 0 and exapnd summation
  have h_sum :
      (∑ i, w.lambda₂ i *
        ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
      ≤ ∑ i, w.lambda₂ i * w.b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (h_mat i) (w.h_nonneg₂ i)
  -- distribute λ₂(i) over the inner addition:
  have h_dist : ∀ i,
      w.lambda₂ i * ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j))
      = (∑ j, w.lambda₂ i * (w.A i j * x j))
      + (∑ j, w.lambda₂ i * (w.A' i j * x' j)) := by
    intro i
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have h_lhs_eq :
      (∑ i, w.lambda₂ i *
        ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
      = (∑ i, ∑ j, w.lambda₂ i * (w.A  i j * x  j))
      + (∑ i, ∑ j, w.lambda₂ i * (w.A' i j * x' j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact h_dist i
  -- simplified now through helper lemma
  have h_swap_A := sum_sum_swap_mul w.lambda₂ w.A x
  have h_swap_A' := sum_sum_swap_mul w.lambda₂ w.A' x'
  -- λ₂ A' = r by definition of r
  have h_lam2A' : ∀ j, (∑ i, w.lambda₂ i * w.A' i j) = w.r j := by
    intro j
    rfl
  -- λ₂ A = -r, derived from h_1c
  have h_lam2A : ∀ j, (∑ i, w.lambda₂ i * w.A i j) = -w.r j := by
    intro j
    have := w.h_1c j
    have h_split :
        (∑ i, w.lambda₂ i * (w.A i j + w.A' i j))
        = (∑ i, w.lambda₂ i * w.A i j) + (∑ i, w.lambda₂ i * w.A' i j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_split, h_lam2A' j] at this
    linarith
  -- rewrite both sums
  have h_lhs_final :
    (∑ i, w.lambda₂ i *
      ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
    = (∑ j, (-w.r j) * x j) + (∑ j, w.r j * x' j) := by
    rw [h_lhs_eq, h_swap_A, h_swap_A']
    simp_rw [h_lam2A, h_lam2A']
  -- λ₂·b = -δ
  have h_rhs : (∑ i, w.lambda₂ i * w.b i) = -w.delta := by
    change _ = -(-(∑ i, w.lambda₂ i * w.b i))
    ring
  -- pull out minus sign
  have h_neg_sum : (∑ j, (-w.r j) * x j) = -(∑ j, w.r j * x j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  -- build h_sum, h_lhs_final, h_rhs, h_neg_sum together
  rw [h_lhs_final] at h_sum
  rw [h_neg_sum, h_rhs] at h_sum
  linarith

/--
This lemma proves:
Any loop-eligible state `env` (one that admits a successor) satisfies
`r · env ≥ δ₀`.
-/
lemma bounded_on_loop_state
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    (env : Env) (h_loop : ∃ env', SemanticStep ip env env') :
    w.delta₀ ≤ ∑ j, w.r j * Env.toVec n env j := by
  -- variable representation of the paper
  obtain ⟨env', h_step⟩ := h_loop
  set x  : Fin n → ℚ := Env.toVec n env  with hx
  set x' : Fin n → ℚ := Env.toVec n env' with hx'
    -- matrix inequality on every row
  have h_mat : ∀ i : Fin m,
      (∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j) ≤ w.b i :=
    step_implies_matrix h_repr h_step
  -- multiply row i by λ₁(i) ≥ 0 and sum.
  have h_sum :
      (∑ i, w.lambda₁ i *
        ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
      ≤ ∑ i, w.lambda₁ i * w.b i := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (h_mat i) (w.h_nonneg₁ i)
  -- expand λ₁
  have h_dist : ∀ i,
      w.lambda₁ i * ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j))
      = (∑ j, w.lambda₁ i * (w.A i j * x j))
      + (∑ j, w.lambda₁ i * (w.A' i j * x' j)) := by
    intro i
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  have h_lhs_eq :
      (∑ i, w.lambda₁ i *
        ((∑ j, w.A i j * x j) + (∑ j, w.A' i j * x' j)))
      = (∑ i, ∑ j, w.lambda₁ i * (w.A i j * x j))
      + (∑ i, ∑ j, w.lambda₁ i * (w.A' i j * x' j)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact h_dist i
  have h_expand :
      (∑ i, ∑ j, w.lambda₁ i * (w.A i j * x j))
      + (∑ i, ∑ j, w.lambda₁ i * (w.A' i j * x' j)) ≤ ∑ i, w.lambda₁ i * w.b i := by
      simpa [h_lhs_eq] using h_sum
  -- now simplified with helper lemma
  have h_swap_A := sum_sum_swap_mul w.lambda₁ w.A x
  have h_swap_A' := sum_sum_swap_mul w.lambda₁ w.A' x'
  have h_zero :
      (∑ i, ∑ j, w.lambda₁ i * (w.A i j * x j))
      ≤ ∑ i, w.lambda₁ i * w.b i := by
    have hp : (∑ i, ∑ j, w.lambda₁ i * (w.A' i j * x' j)) = 0 := by
      rw [h_swap_A']
      apply Finset.sum_eq_zero
      intro j _
      rw [w.h_1a j, zero_mul]
    rw [hp, add_zero] at h_expand
    exact h_expand
  -- λ₁A = λ₂A (using 1b)
  have h_eq : ∀ j, (∑ i, w.lambda₁ i * w.A i j) = (∑ i, w.lambda₂ i * w.A i j) := by
    intro j
    have h := w.h_1b j
    have h_split :
        (∑ i, (w.lambda₁ i - w.lambda₂ i) * w.A i j)
        = (∑ i, w.lambda₁ i * w.A i j) - (∑ i, w.lambda₂ i * w.A i j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_split] at h
    linarith
  -- λ₂ A = -r  (using 1c)
  have h_lam2A : ∀ j, (∑ i, w.lambda₂ i * w.A i j) = -w.r j := by
    intro j
    have hc := w.h_1c j
    have hc_split :
        (∑ i, w.lambda₂ i * (w.A i j + w.A' i j))
        = (∑ i, w.lambda₂ i * w.A i j) + (∑ i, w.lambda₂ i * w.A' i j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h_lam2A' : (∑ i, w.lambda₂ i * w.A' i j) = w.r j := rfl
    rw [hc_split, h_lam2A'] at hc
    linarith
  -- combine to λ₁ A = -r
  have h_lam1A : ∀ j, (∑ i, w.lambda₁ i * w.A i j) = -w.r j := by
    intro j
    rw [h_eq j, h_lam2A j]
  rw [h_swap_A] at h_zero
  -- replace inner sum column
  have h_lhs_r : (∑ j, (∑ i, w.lambda₁ i * w.A i j) * x j)
               = ∑ j, (-w.r j) * x j := by
    apply Finset.sum_congr rfl
    intro j _
    rw [h_lam1A j]
  rw [h_lhs_r] at h_zero
  -- pull minus sign out
  have h_neg : (∑ j, (-w.r j) * x j) = -(∑ j, w.r j * x j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_neg] at h_zero
  -- rhs is -δ₀ by definition of δ₀
  have h_rhs : (∑ i, w.lambda₁ i * w.b i) = -w.delta₀ := by
    unfold FarkasWitness.delta₀
    ring
  rw [h_rhs] at h_zero
  linarith

/--
The ranking function ρ from the paper.
-/
noncomputable def FarkasWitness.rho
    {n m : ℕ} (w : FarkasWitness n m) (ip : IntegerProgram) (env : Env) : ℚ :=
  letI : Decidable (∃ env', SemanticStep ip env env') := Classical.propDecidable _
  if (∃ env', SemanticStep ip env env') then
    ∑ j, w.r j * Env.toVec n env j
  else
    w.delta₀ - w.delta

/- adr
This lemma shows that ρ strictly decreases by at least δ on every step.
This can be transformed into the statement ρ(x') ≤ ρ(x) - δ, which shows this property.
It works whith splitting into two cases:
Case 1: x' has a successor
Then ρ(x') = r·x', this can be resolved by `decrease_on_step` since it solves exactly rx' ≤ rx - δ
Case 2: x' has no succesor
Then ρ(x') = δ₀ - δ, which means δ₀ - δ ≤ rx - δ
Which is equivalent to: δ₀ ≤ rx which can be solved by `bounded_on_loop_state`
With calculation: (ρ(x) ≥ δ₀ - δ ⇒ rx ≥ δ₀ - δ ⇒ rx ≥ δ₀).
-/
lemma rho_strict_decrease
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    {env env' : Env} (h_step : SemanticStep ip env env') :
    w.rho ip env' ≤ w.rho ip env - w.delta := by
  have h_env_loop : ∃ e', SemanticStep ip env e' := ⟨env', h_step⟩
  unfold FarkasWitness.rho
  rw [if_pos h_env_loop]
  by_cases h_env'_loop : ∃ e'', SemanticStep ip env' e''
  · rw [if_pos h_env'_loop]
    exact decrease_on_step h_repr h_step
  · rw [if_neg h_env'_loop]
    have h_bound : w.delta₀ ≤ ∑ j, w.r j * Env.toVec n env j :=
      bounded_on_loop_state h_repr env h_env_loop
    linarith

/- adr
This lemma proves ρ is bounded below by δ₀ - δ on every state.
It can be transformed into the statement ρ(x) ≥ δ₀ - δ.
It works again with splitting into two cases:
Case 1: x has a successor
Since we have a successor ρ(x) = rx, we want to show rx ≥ δ₀ - δ
`bounded_on_loop_state` gives us rx ≥ δ₀ => rx ≥ δ₀ - δ (since δ > 0)
Case 2: x has no successor
This is trivial since ρ(x) = δ₀ - δ.

-/
lemma rho_lower_bound
    {n m : ℕ} {ip : IntegerProgram} {w : FarkasWitness n m}
    (h_repr : w.RepresentsProgram ip)
    (env : Env) :
    w.delta₀ - w.delta ≤ w.rho ip env := by
  unfold FarkasWitness.rho
  by_cases h_env: ∃ e', SemanticStep ip env e'
  · rw [if_pos h_env]
    have h_bound : w.delta₀ ≤ ∑ j, w.r j * Env.toVec n env j :=
      bounded_on_loop_state h_repr env h_env
    have h_mec : w.delta₀ ≤ ∑ j, w.r j * Env.toVec n env j + w.delta :=
      le_trans h_bound (le_add_of_nonneg_right (le_of_lt w.delta_pos))
    simpa
  · rw [if_neg h_env]

/- adr
This lemma shows us that a well-definied ranking functions (strict decrease, lower bound) result in bound SemanticPaths.
For this proof we need as setup:
- the ranking funciton: ρ
- the lower bound: L which is ℚ
- the value of minimum decrease: δ which is ℚ
- the statement of decrease: h_decrease
 -> it tells us that if there is a SemanticStep then the resulting value of the ranking function is at least smaller than the previous value minus δ
- a path, which length we want to have bound: p

And the statement we prove: p.length · δ ≤ ρ(env) - L
Is derived from: ρ(env_start)-ρ(final_env) ≥ p.length · δ
Since the lower bound L: ρ(final_env) ≥ L you can simplyfiy to: ρ(env) - L ≥ p.length · δ
The next lemma: `path_length_le_bound` shows why this makes it bound, but conceptionally we receive: p.length ≤ (ρ(env) - L) / δ, which is exactly our searched n ∈ ℕ.

The proof outline by induction over the SemanticPath:
- The base-case has length zero, thus we have 0 ≤ ρ(env) - L, which is closed by h_bound.
- The recursive case:
Out of the Paths recursive information, we can construct a SemanticStep.
With h_decrease, we can infere that this step decreases as wanted.
And then prove the statement by calculating this equation:
(1 + p'.length) · δ
= δ + p'.length · δ
≤ δ + (p(env') - L)
≤ δ + (ρ(env) - δ) - L
= ρ(env) - L
-/
lemma path_length_bounded_by_ranking
    (ip : IntegerProgram)
    (ρ : Env → ℚ) (L δ : ℚ)
    (h_bound : ∀ env, L ≤ ρ env)
    (h_decrease : ∀ env env', SemanticStep ip env env' → ρ env' ≤ ρ env - δ)
    {env : Env} {u v : Nat} (p : SemanticPath ip env u v) :
    (p.length : ℚ) * δ ≤ ρ env - L := by
  induction p with
  | nil u env h =>
    rw [SemanticPath.length, Nat.cast_zero, zero_mul, sub_nonneg]
    exact h_bound env
  | cons env t h_edge hguard env' hupdate p' ih =>
    have h_step : SemanticStep ip env env' :=
      ⟨t, h_edge, hguard, hupdate⟩
    have h_dec : ρ env' ≤ ρ env - δ := h_decrease env env' h_step
    rw [SemanticPath.length]
    have h_fin : ((1 + p'.length : ℕ) : ℚ) * δ = δ + (p'.length : ℚ) * δ := by
      push_cast
      ring
    linarith [ih, h_dec]

/- adr
This lemma generalizes the results of `path_length_bounded_by_ranking` to create an existential statement.
Since we proved: p.length · δ  ≤ ρ(env) - L, we can create the witness: p.length ≤ (ρ(env) - L) / δ (roundend up)
Implementation:
We receive the result by providing all the necessary evidence to the previous lemma.
Then we devide we recreate the witness by deviding δ (h_div) and then ceil it, which already proves the goal.
-/
lemma path_length_le_bound
    (ip : IntegerProgram)
    (ρ : Env → ℚ) (L δ : ℚ) (hδ : 0 < δ)
    (h_bound : ∀ env, L ≤ ρ env)
    (h_decrease : ∀ env env', SemanticStep ip env env' → ρ env' ≤ ρ env - δ)
    (env : Env) :
    ∃ n : Nat, ∀ {u v : Nat} (p : SemanticPath ip env u v), p.length ≤ n := by
  use ⌈(ρ env - L) / δ⌉₊
  intro u v p
  have h_rank : (p.length : ℚ) * δ ≤ ρ env - L :=
    path_length_bounded_by_ranking ip ρ L δ h_bound h_decrease p
  have h_div : (p.length : ℚ) ≤ (ρ env - L) / δ := by
    rw [le_div_iff₀ hδ]
    exact h_rank
  have ceil : (p.length : ℚ) ≤ (⌈(ρ env - L) / δ⌉₊ : ℚ) :=
    le_trans h_div (Nat.le_ceil _)
  exact_mod_cast ceil

/--
If a Farkas witness `w` represents `ip`, then `ip` terminates.
-/
theorem termination_of_farkas_witness
    {n m : ℕ} {ip : IntegerProgram}
    (w : FarkasWitness n m) (h_repr : w.RepresentsProgram ip) :
    ip.Termination := by
  intro env
  exact path_length_le_bound
    ip
    (w.rho ip)
    (w.delta₀ - w.delta)
    w.delta
    w.delta_pos
    (rho_lower_bound h_repr)
    (fun _ _ h => rho_strict_decrease h_repr h)
    env

end LASW
