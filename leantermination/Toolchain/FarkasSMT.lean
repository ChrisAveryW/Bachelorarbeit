import leantermination.Datastructures.IntegerProgram
import Std

set_option linter.unusedVariables false

/-!
# Farkas / Podelski–Rybalchenko SMT encoding for (self-)loops

This file replaces the former `linear_expression.lean` and `termination_lasw.lean`.

For a single transition it builds the SMT-LIB feasibility query of the linear
ranking-function conditions of *"A Complete Method for the Synthesis of Linear
Ranking Functions"*. The encoding is aligned with `LASW.FarkasWitness`
(see `LASWTermination.lean`): the unknowns handed to Z3 are the two non-negative
multiplier vectors `λ₁, λ₂`, the transition relation is the polyhedron
`A·x + A'·x' ≤ b`, and the assertions are exactly conditions (1a)–(1d).

Pipeline entry point: `IntegerProgram.checkSelfLoops` asks Z3 for a ranking
function of every self-loop of a program. A `sat` verdict for a loop means a
linear ranking function for that loop exists.

Nothing here produces a `FarkasWitness` *term*; turning a `sat` answer into the
`h_witnesses` hypothesis of `terminates_of_selfloops_rank` is the separate
`sat ⟹ ∃ FarkasWitness` bridge, deliberately kept out of this file.
-/

/-! ## 1. Linear normalization of expressions

`LinExpr` is the canonical linear form `∑ⱼ coeffs[j]·xⱼ + const`. It is the bridge
from the syntactic `Expr` tree to the numeric coefficient form the matrix
encoding needs. -/

structure LinExpr where
  coeffs : List Int   -- coeffs[j] is the coefficient of variable xⱼ
  const  : Int        -- the constant term
deriving Repr

namespace LinExpr

def ofLit (c : Int) : LinExpr := { coeffs := [], const := c }

def ofVar (i : Nat) : LinExpr := { coeffs := List.replicate i 0 ++ [1], const := 0 }

/-- Zip two coefficient lists of possibly different length, padding with `0`. -/
private def zipDefault (f : Int → Int → Int) : List Int → List Int → List Int
  | [],      ys      => ys.map (f 0)
  | xs,      []      => xs.map (f · 0)
  | x :: xs, y :: ys => f x y :: zipDefault f xs ys

def add (a b : LinExpr) : LinExpr :=
  { coeffs := zipDefault (· + ·) a.coeffs b.coeffs, const := a.const + b.const }

def sub (a b : LinExpr) : LinExpr :=
  { coeffs := zipDefault (· - ·) a.coeffs b.coeffs, const := a.const - b.const }

def scale (k : Int) (a : LinExpr) : LinExpr :=
  { coeffs := a.coeffs.map (· * k), const := a.const * k }

/-- Multiplication is linear only when at least one factor is a constant. -/
def mul (a b : LinExpr) : Option LinExpr :=
  if a.coeffs.isEmpty then some (scale a.const b)
  else if b.coeffs.isEmpty then some (scale b.const a)
  else none

end LinExpr

/-- Normalize an `Expr` into a `LinExpr`, or `none` if the expression is non-linear. -/
def Expr.toLin : Expr → Option LinExpr
  | .lit n   => some (LinExpr.ofLit n)
  | .var i   => some (LinExpr.ofVar i)
  | .add a b => do return LinExpr.add (← a.toLin) (← b.toLin)
  | .sub a b => do return LinExpr.sub (← a.toLin) (← b.toLin)
  | .mul a b => do LinExpr.mul (← a.toLin) (← b.toLin)

/-- Highest variable index used by an expression, plus one (`0` if variable-free). -/
def Expr.varBound : Expr → Nat
  | .lit _   => 0
  | .var i   => i + 1
  | .add a b => max a.varBound b.varBound
  | .sub a b => max a.varBound b.varBound
  | .mul a b => max a.varBound b.varBound

/-- Highest variable index used by a constraint, plus one. -/
def Constraint.varBound : Constraint → Nat
  | .atom _ a b => max a.varBound b.varBound
  | .not c      => c.varBound
  | .and c1 c2  => max c1.varBound c2.varBound

/-- Number of program variables involved in a transition (highest index + 1),
    taking the guard, every update's target `pv`, and every update expression
    into account. -/
def Transition.numVars (t : Transition) : Nat :=
  t.update.foldl (fun acc u => max acc (max (u.pv + 1) u.expr.varBound))
    t.guard.varBound

/-! ## 2. Matrix rows

A `Row` represents one inequality `∑ⱼ a[j]·xⱼ + ∑ⱼ a'[j]·x'ⱼ ≤ b` of the
transition relation `A·x + A'·x' ≤ b`. Missing coefficients default to `0`. -/

structure Row where
  a  : List Int   -- coefficients on the pre-state variables x
  a' : List Int   -- coefficients on the post-state variables x'
  b  : Int        -- right-hand side
deriving Repr

namespace Row

def aCoeff  (r : Row) (j : Nat) : Int := r.a.getD j 0
def a'Coeff (r : Row) (j : Nat) : Int := r.a'.getD j 0

end Row

private def negList (xs : List Int) : List Int := xs.map (fun c => -c)

/-- Rows produced by a guard. Returns `none` for guards that are not a
    conjunction of linear (in)equalities (e.g. disjunctions, disequalities,
    non-linear atoms). -/
def guardRows : Constraint → Option (List Row)
  | .atom .lt lhs rhs => do
      -- lhs < rhs  ⟺  (lhs - rhs) + 1 ≤ 0   (integer tightening)
      let d ← (Expr.sub lhs rhs).toLin
      pure [{ a := d.coeffs, a' := [], b := -(d.const + 1) }]
  | .atom .eq lhs rhs => do
      -- lhs = rhs  ⟺  (lhs - rhs) ≤ 0  ∧  -(lhs - rhs) ≤ 0
      let d ← (Expr.sub lhs rhs).toLin
      pure [ { a := d.coeffs,          a' := [], b := -d.const }
           , { a := negList d.coeffs,  a' := [], b := d.const  } ]
  | .not (.atom .lt a b) => do
      -- ¬(a < b)  ⟺  b ≤ a  ⟺  (b - a) ≤ 0     (covers ≤, ≥, > derived guards)
      let d ← (Expr.sub b a).toLin
      pure [{ a := d.coeffs, a' := [], b := -d.const }]
  | .not (.not c) => guardRows c
  | .and c1 c2 => do
      let r1 ← guardRows c1
      let r2 ← guardRows c2
      pure (r1 ++ r2)
  | _ => none

/-- Defining expression of `x'ᵢ` under the transition: the update's expression if
    variable `i` is assigned, otherwise the identity `xᵢ` (variable unchanged). -/
def Transition.postExpr (t : Transition) (i : Nat) : Expr :=
  match t.update.find? (fun u => u.pv == i) with
  | some u => u.expr
  | none   => Expr.var i

/-- Every row encoding the transition relation `A·x + A'·x' ≤ b`, or `none` if the
    guard is unsupported. For each variable `i` an equation `x'ᵢ = fᵢ(x)` is split
    into two `≤` rows; unchanged variables get the identity `x'ᵢ = xᵢ`. -/
def Transition.toRows (t : Transition) : Option (List Row) := do
  let n := t.numVars
  let gRows ← guardRows t.guard
  let uRowGroups ← (List.range n).mapM (fun i => do
    let f ← (t.postExpr i).toLin
    -- x'ᵢ = f(x)  ⟺  f(x) - x'ᵢ ≤ 0  ∧  x'ᵢ - f(x) ≤ 0
    let ei : List Int := List.replicate i 0 ++ [1]   -- unit vector for x'ᵢ
    pure [ ({ a := f.coeffs,         a' := negList ei, b := -f.const } : Row)
         , ({ a := negList f.coeffs, a' := ei,         b := f.const  } : Row) ])
  pure (gRows ++ uRowGroups.flatten)

/-! ## 3. SMT-LIB encoding of conditions (1a)–(1d) -/

/-- Render an integer as an SMT-LIB term (negatives become `(- k)`). -/
private def intSMT (k : Int) : String :=
  if k < 0 then s!"(- {-k})" else toString k

/-- Sum of already-rendered terms, dropping to `0`/the single term when short. -/
private def smtSum (terms : List String) : String :=
  match terms with
  | []  => "0"
  | [t] => t
  | _   => "(+ " ++ String.intercalate " " terms ++ ")"

private def lam1 (i : Nat) : String := s!"l1_{i}"
private def lam2 (i : Nat) : String := s!"l2_{i}"

/-- The full SMT-LIB query asserting the Podelski–Rybalchenko conditions for the
    relation given by `rows` over `n` variables. Unknowns: `λ₁, λ₂ ≥ 0`. -/
def farkasQuery (rows : List Row) (n : Nat) : String :=
  let m := rows.length
  let indexed := rows.zip (List.range m)   -- (row, its λ-index)
  -- ∑ᵢ coeff(rowᵢ) · varName(i), skipping zero coefficients
  let sumOver : (Nat → String) → (Row → Int) → String := fun varName coeff =>
    smtSum (indexed.filterMap (fun (r, i) =>
      let c := coeff r
      if c == 0 then none else some s!"(* {intSMT c} {varName i})"))
  -- (1a) ∀ j, ∑ᵢ λ₁ᵢ · A'ᵢⱼ = 0
  let c1a := (List.range n).map (fun j =>
    s!"(assert (= {sumOver lam1 (fun r => r.a'Coeff j)} 0))")
  -- (1b) ∀ j, ∑ᵢ (λ₁ᵢ - λ₂ᵢ) · Aᵢⱼ = 0
  let c1b := (List.range n).map (fun j =>
    s!"(assert (= (- {sumOver lam1 (fun r => r.aCoeff j)} {sumOver lam2 (fun r => r.aCoeff j)}) 0))")
  -- (1c) ∀ j, ∑ᵢ λ₂ᵢ · (Aᵢⱼ + A'ᵢⱼ) = 0
  let c1c := (List.range n).map (fun j =>
    s!"(assert (= {sumOver lam2 (fun r => r.aCoeff j + r.a'Coeff j)} 0))")
  -- (1d) ∑ᵢ λ₂ᵢ · bᵢ < 0
  let c1d := s!"(assert (< {sumOver lam2 (fun r => r.b)} 0))"
  let decls := (List.range m).map (fun i =>
    s!"(declare-const {lam1 i} Real)\n(declare-const {lam2 i} Real)")
  let nonneg := (List.range m).map (fun i =>
    s!"(assert (>= {lam1 i} 0))\n(assert (>= {lam2 i} 0))")
  String.intercalate "\n"
    (["(set-logic QF_LRA)", ""] ++ decls ++ [""] ++ nonneg ++ [""]
      ++ c1a ++ c1b ++ c1c ++ [c1d] ++ ["", "(check-sat)"])

/-- SMT-LIB ranking-function query for a single transition, or `none` if the
    guard is unsupported. -/
def Transition.toFarkasSMT (t : Transition) : Option String := do
  let rows ← t.toRows
  pure (farkasQuery rows t.numVars)

/-! ## 4. Running Z3 over the self-loops of a program -/

inductive Z3Result where
  | sat | unsat | unknown
  | error (msg : String)
deriving Repr, DecidableEq, BEq

def Z3Result.toString : Z3Result → String
  | .sat     => "sat"
  | .unsat   => "unsat"
  | .unknown => "unknown"
  | .error m => s!"error: {m}"

instance : ToString Z3Result := ⟨Z3Result.toString⟩

/-- Interpret Z3's textual output; the verdict is on the first line. -/
def parseZ3 (stdout stderr : String) : Z3Result :=
  match (stdout.trimAscii.toString.splitOn "\n").headD "" |>.trimAscii.toString with
  | "sat"     => .sat
  | "unsat"   => .unsat
  | "unknown" => .unknown
  | ""        => .error (if stderr.trimAscii.toString.isEmpty then "no output from z3"
                         else stderr.trimAscii.toString)
  | other     => .error other

/-- Write a query to a temp file, invoke `z3`, and parse the result. -/
def runZ3 (smt : String) : IO Z3Result := do
  try
    let path := "/tmp/leantermination_query.smt2"
    IO.FS.writeFile path smt
    let out ← IO.Process.output { cmd := "z3", args := #[path] }
    pure (parseZ3 out.stdout out.stderr)
  catch e =>
    pure (.error (toString e))

/-- The self-loops of a program: edges whose source equals their target. -/
def IntegerProgram.selfLoopEdges (ip : IntegerProgram) : List Transition :=
  ip.edges.filter (fun t => t.src == t.tgt)

/-- **Pipeline core.** For every self-loop of `ip`, build its Farkas
    ranking-function query and ask Z3. Returns each self-loop paired with the
    solver verdict; `sat` means a linear ranking function for that loop exists. -/
def IntegerProgram.checkSelfLoops (ip : IntegerProgram) :
    IO (List (Transition × Z3Result)) :=
  ip.selfLoopEdges.mapM (fun t =>
    match t.toFarkasSMT with
    | none     => pure (t, Z3Result.error "unsupported (non-linear / non-conjunctive) guard")
    | some smt => do pure (t, ← runZ3 smt))

/-- `true` iff Z3 finds a ranking function (`sat`) for *every* self-loop. -/
def IntegerProgram.allSelfLoopsRank (ip : IntegerProgram) : IO Bool := do
  let results ← ip.checkSelfLoops
  pure (results.all (fun (_, r) => r == Z3Result.sat))
