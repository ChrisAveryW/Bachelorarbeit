import leantermination.Datastructures.IntegerProgram
import Std

set_option linter.unusedVariables false

/-!
The FarkasWitness can be converted into an SMT-Expression understood by Z3.
All related functions and structures have the purpose of efficiently creating an SMT expression.
-/

/-
This is an intermediate structure derived from `Expr`.
-/
structure LinExpr where
  coeffs : List Int   -- coeffs[j] is the coefficient of variable xⱼ
  const  : Int        -- the constant term
deriving Repr

namespace LinExpr

def ofLit (c : Int) : LinExpr := { coeffs := [], const := c }

def ofVar (i : Nat) : LinExpr := { coeffs := List.replicate i 0 ++ [1], const := 0 }

-- zip two coefficient lists of possibly different length, padding with of zeros
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

-- one factor is a constant
def mul (a b : LinExpr) : Option LinExpr :=
  if a.coeffs.isEmpty then some (scale a.const b)
  else if b.coeffs.isEmpty then some (scale b.const a)
  else none

end LinExpr

-- create LinExpr from Expr
def Expr.toLin : Expr → Option LinExpr
  | .lit n   => some (LinExpr.ofLit n)
  | .var i   => some (LinExpr.ofVar i)
  | .add a b => do return LinExpr.add (← a.toLin) (← b.toLin)
  | .sub a b => do return LinExpr.sub (← a.toLin) (← b.toLin)
  | .mul a b => do LinExpr.mul (← a.toLin) (← b.toLin)

-- highest index
def Expr.varBound : Expr → Nat
  | .lit _   => 0
  | .var i   => i + 1
  | .add a b => max a.varBound b.varBound
  | .sub a b => max a.varBound b.varBound
  | .mul a b => max a.varBound b.varBound

-- highest index, for constraints
def Constraint.varBound : Constraint → Nat
  | .atom _ a b => max a.varBound b.varBound
  | .not c      => c.varBound
  | .and c1 c2  => max c1.varBound c2.varBound

-- highest index, of transition
def Transition.numVars (t : Transition) : Nat :=
  t.update.foldl (fun acc u => max acc (max (u.pv + 1) u.expr.varBound))
    t.guard.varBound

/-
This represents one row of the linear inequality: A·x + A'·x ≤ b.
-/
structure Row where
  a  : List Int   -- coefficients on the vector x
  a' : List Int   -- coefficients on the vector x'
  b  : Int        -- rhs
deriving Repr

namespace Row

def aCoeff  (r : Row) (j : Nat) : Int := r.a.getD j 0
def a'Coeff (r : Row) (j : Nat) : Int := r.a'.getD j 0

end Row

private def negList (xs : List Int) : List Int := xs.map (fun c => -c)

/--
This creates rows for the guards, or none if the FarkasWitness cannot represent this constraint (e.g. disjunctions)
-/
def guardRows : Constraint → Option (List Row)
  | .atom .lt lhs rhs => do -- lhs < rhs  ⟺  (lhs - rhs) + 1 ≤ 0
      let d ← (Expr.sub lhs rhs).toLin
      pure [{ a := d.coeffs, a' := [], b := -(d.const + 1) }]
  | .atom .eq lhs rhs => do -- lhs = rhs  ⟺  (lhs - rhs) ≤ 0  ∧  -(lhs - rhs) ≤ 0
      let d ← (Expr.sub lhs rhs).toLin
      pure [ { a := d.coeffs,          a' := [], b := -d.const }
           , { a := negList d.coeffs,  a' := [], b := d.const  } ]
  | .not (.atom .lt a b) => do -- ¬(a < b)  ⟺  b ≤ a  ⟺  (b - a) ≤ 0
      let d ← (Expr.sub b a).toLin
      pure [{ a := d.coeffs, a' := [], b := -d.const }]
  | .not (.not c) => guardRows c
  | .and c1 c2 => do
      let r1 ← guardRows c1
      let r2 ← guardRows c2
      pure (r1 ++ r2)
  | _ => none

-- adr: This makes transitions updates total, thus not-updated variables are just the identity
/--
Returns the update Expr for a transition, extended to cover all variables.
-/
def Transition.postExpr (t : Transition) (i : Nat) : Expr :=
  match t.update.find? (fun u => u.pv == i) with
  | some u => u.expr
  | none   => Expr.var i


/- adr
To linearize a transition, we need to handle guard and updates.
  - guard: for this we can use the guardRows function
  - updates: for every variable i do
    - get the update expression
    - linearize it
    - ei is the unit vector that is needed to fix x'i
    - use: x'ᵢ = f(x)  ⟺  f(x) - x'ᵢ ≤ 0  ∧  x'ᵢ - f(x) ≤ 0 to create rows
-/
/--
This crates all necessary rows for a Transition. It also expects the number of program variables n.
-/
def Transition.toRowsN (t : Transition) (n : Nat) : Option (List Row) := do
  let gRows ← guardRows t.guard
  let uRowGroups ← (List.range n).mapM (fun i => do
    let f ← (t.postExpr i).toLin
    let ei : List Int := List.replicate i 0 ++ [1]   -- unit vector for x'ᵢ
    pure [ ({ a := f.coeffs,         a' := negList ei, b := -f.const } : Row)
         , ({ a := negList f.coeffs, a' := ei,         b := f.const  } : Row) ])
  pure (gRows ++ uRowGroups.flatten)

/--
This creates all necessary rows for a Transition. It identifies the number of program variables and uses `Transition.toRowN`.
-/
def Transition.toRows (t : Transition) : Option (List Row) := t.toRowsN t.numVars

/-! Z3 encodings -/

-- adr: there are no negative literals, there only is the application minus on a positive literal
private def intSMT (k : Int) : String :=
  if k < 0 then s!"(- {-k})" else toString k

-- sum up some arithmetic terms
private def smtSum (terms : List String) : String :=
  match terms with
  | []  => "0"
  | [t] => t
  | _   => "(+ " ++ String.intercalate " " terms ++ ")"

private def lam1 (i : Nat) : String := s!"l1_{i}"
private def lam2 (i : Nat) : String := s!"l2_{i}"

/--
  This is the complete SMT query, which creates Podelski–Rybalchenko conditions for the given rows (consistent of n variables).
-/
def farkasQuery (rows : List Row) (n : Nat) : String :=
  let m := rows.length
  let indexed := rows.zip (List.range m)   -- (row, its λ-index)
  -- ∑ᵢ coeff(rowᵢ) · varName(i)
  -- skips zeros
  let sumOver : (Nat → String) → (Row → Int) → String := fun varName coeff =>
    smtSum (indexed.filterMap (fun (r, i) =>
      let c := coeff r
      if c == 0 then none else some s!"(* {intSMT c} {varName i})"))
  -- Conditions of Paper:
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

/--
  This function creates a SMT-String from a Transition.
-/
def Transition.toFarkasSMT (t : Transition) : Option String := do
  let rows ← t.toRows
  pure (farkasQuery rows t.numVars)

/-- Structure to parse Z3's result -/
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

/-- Interpret Z3's result -/
def parseZ3 (stdout stderr : String) : Z3Result :=
  match (stdout.trimAscii.toString.splitOn "\n").headD "" |>.trimAscii.toString with
  | "sat"     => .sat
  | "unsat"   => .unsat
  | "unknown" => .unknown
  | ""        => .error (if stderr.trimAscii.toString.isEmpty then "no output from z3"
                         else stderr.trimAscii.toString)
  | other     => .error other

/-- This function writes SMT-query to temporary file, runs Z3 and retrieves the output. -/
def runZ3 (smt : String) : IO Z3Result := do
  try
    let path := "/tmp/leantermination_query.smt2"
    IO.FS.writeFile path smt
    let out ← IO.Process.output { cmd := "z3", args := #[path] }
    pure (parseZ3 out.stdout out.stderr)
  catch e =>
    pure (.error (toString e))

-- Self-loops: @todo make uniform, already exists in SelfLoopTermination.lean
-- import breaks, if you import selflooptermination...
def IntegerProgram.selfLoopEdges (ip : IntegerProgram) : List Transition :=
  ip.edges.filter (fun t => t.src == t.tgt)

/--
Main pipeline step: check every self-loop, and see if Z3 produces a model.
-/
def IntegerProgram.checkSelfLoops (ip : IntegerProgram) :
    IO (List (Transition × Z3Result)) :=
  ip.selfLoopEdges.mapM (fun t =>
    match t.toFarkasSMT with
    | none     => pure (t, Z3Result.error "unsupported (non-linear / non-conjunctive) guard")
    | some smt => do pure (t, ← runZ3 smt))

/-- This function returns true, if all self-loops have a ranking function. -/
def IntegerProgram.allSelfLoopsRank (ip : IntegerProgram) : IO Bool := do
  let results ← ip.checkSelfLoops
  pure (results.all (fun (_, r) => r == Z3Result.sat))
