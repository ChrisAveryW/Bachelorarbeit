import leantermination.Datastructures.IntegerProgram
import leantermination.Parsing.Z3Parse
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

/-! Check the Z3 Model, verify the answer as a certificate. -/

structure FarkasCert where
  rows : List Row
  n    : Nat
  lam1 : List Rat   -- λ₁, one entry per row
  lam2 : List Rat   -- λ₂, one entry per row
deriving Repr

private def ratNonneg (r : Rat) : Bool := !(Rat.blt r 0)   -- 0 ≤ r
private def ratNeg    (r : Rat) : Bool := Rat.blt r 0       -- r < 0
private def ratIsZero (r : Rat) : Bool := r.num == 0        -- r = 0

/-- Column-wise weighted sum `∑ᵢ λᵢ · coeff(rowᵢ)` over the rationals. -/
private def ratDot (lam : List Rat) (rows : List Row) (coeff : Row → Int) : Rat :=
  (rows.zip lam).foldl (fun acc (r, l) => acc + l * Rat.ofInt (coeff r)) 0

/-- Independent verification of a certificate: recompute conditions (1a)–(1d) on
    the concrete `λ` values. This is `LASW.FarkasWitness`'s hypotheses made
    executable — a `true` result means the model really is a Farkas witness. -/
def FarkasCert.check (c : FarkasCert) : Bool :=
  let m := c.rows.length
  -- shapes and non-negativity  (↔ h_nonneg₁, h_nonneg₂)
  c.lam1.length == m && c.lam2.length == m
    && c.lam1.all ratNonneg && c.lam2.all ratNonneg
    -- (1a) ∑ᵢ λ₁ᵢ·A'ᵢⱼ = 0, (1b) ∑ᵢ(λ₁ᵢ-λ₂ᵢ)·Aᵢⱼ = 0, (1c) ∑ᵢ λ₂ᵢ·(A+A')ᵢⱼ = 0
    && (List.range c.n).all (fun j =>
          ratIsZero (ratDot c.lam1 c.rows (·.a'Coeff j))
       && ratIsZero (ratDot c.lam1 c.rows (·.aCoeff j)
                       - ratDot c.lam2 c.rows (·.aCoeff j))
       && ratIsZero (ratDot c.lam2 c.rows (fun r => r.aCoeff j + r.a'Coeff j)))
    -- (1d) ∑ᵢ λ₂ᵢ·bᵢ < 0
    && ratNeg (ratDot c.lam2 c.rows (·.b))

/-- Coefficients of the synthesized ranking function `r := λ₂·A'` (cf.
    `LASW.FarkasWitness.r`). -/
def FarkasCert.rankingCoeff (c : FarkasCert) (j : Nat) : Rat :=
  ratDot c.lam2 c.rows (·.a'Coeff j)

/-- Strict decrease amount `δ := -(λ₂·b)` (cf. `LASW.FarkasWitness.delta`). -/
def FarkasCert.delta (c : FarkasCert) : Rat := -(ratDot c.lam2 c.rows (·.b))

/-- Lower-bound constant `δ₀ := -(λ₁·b)` (cf. `LASW.FarkasWitness.delta₀`). -/
def FarkasCert.delta0 (c : FarkasCert) : Rat := -(ratDot c.lam1 c.rows (·.b))

/-- Human-readable form of the synthesized ranking function and its constants. -/
def FarkasCert.rankingString (c : FarkasCert) : String :=
  let terms := (List.range c.n).filterMap (fun j =>
    let rj := c.rankingCoeff j
    if rj.num == 0 then none else some s!"({rj})·x{j}")
  let body := if terms.isEmpty then "0" else String.intercalate " + " terms
  s!"r(x) = {body}   (δ = {c.delta}, δ₀ = {c.delta0})"

/-! ## 6. Model-reading pipeline: sat ⟹ read model ⟹ check witness

The `(get-model)` reply is parsed by `parseModel` (see
`leantermination.Parsing.Z3Parse`) into `name ↦ Rat` bindings. -/

/-- Ranking-function query that also requests the model on `sat`. -/
def Transition.toFarkasSMTModel (t : Transition) : Option String := do
  let rows ← t.toRows
  pure ("(set-option :produce-models true)\n"
        ++ farkasQuery rows t.numVars ++ "\n(get-model)")

/-- Run Z3, and on `sat` also parse the returned model bindings. -/
def runZ3WithModel (smt : String) : IO (Z3Result × List (String × Rat)) := do
  try
    let path := "/tmp/leantermination_query.smt2"
    IO.FS.writeFile path smt
    let out ← IO.Process.output { cmd := "z3", args := #[path] }
    let res := parseZ3 out.stdout out.stderr
    let model := if res == Z3Result.sat then parseModel out.stdout else []
    pure (res, model)
  catch e =>
    pure (.error (toString e), [])

/-- Assemble a certificate from `rows`, the variable count, and Z3's model,
    looking up `l1_i`/`l2_i` per row (defaulting to `0` if absent). -/
def FarkasCert.ofModel (rows : List Row) (n : Nat)
    (model : List (String × Rat)) : FarkasCert :=
  let m := rows.length
  let get (name : String) : Rat :=
    (model.find? (fun p => p.1 == name)).map (·.2) |>.getD 0
  { rows := rows, n := n,
    lam1 := (List.range m).map (fun i => get s!"l1_{i}"),
    lam2 := (List.range m).map (fun i => get s!"l2_{i}") }

/-- Outcome of the full synthesize-and-verify step for one self-loop. -/
inductive WitnessCheck where
  | unsupported                         -- guard not linear / conjunctive
  | noRank                              -- Z3: unsat
  | unknown                             -- Z3: unknown
  | verified        (cert : FarkasCert) -- sat, and the model passed our check
  | modelUnverified (cert : FarkasCert) -- sat, but the model failed our check
  | solverError     (msg : String)
deriving Repr

/-- `true` only when a certificate was produced *and* independently verified. -/
def WitnessCheck.isVerified : WitnessCheck → Bool
  | .verified _ => true
  | _           => false

/-- **Extended pipeline core.** Build the ranking query for `t`, ask Z3, and on
    `sat` read the model back and re-check the Farkas conditions against it. -/
def Transition.checkFarkasWitness (t : Transition) : IO WitnessCheck := do
  match t.toRows with
  | none      => pure .unsupported
  | some rows =>
      let smt := "(set-option :produce-models true)\n"
                   ++ farkasQuery rows t.numVars ++ "\n(get-model)"
      let (res, model) ← runZ3WithModel smt
      match res with
      | .unsat   => pure .noRank
      | .unknown => pure .unknown
      | .error m => pure (.solverError m)
      | .sat     =>
          let cert := FarkasCert.ofModel rows t.numVars model
          pure (if cert.check then .verified cert else .modelUnverified cert)

/-- For every self-loop of `ip`, synthesize a Farkas witness with Z3 and verify
    it independently. Companion to `checkSelfLoops` that returns the checked
    certificate rather than just the raw verdict. -/
def IntegerProgram.checkSelfLoopsWitness (ip : IntegerProgram) :
    IO (List (Transition × WitnessCheck)) :=
  ip.selfLoopEdges.mapM (fun t => do pure (t, ← t.checkFarkasWitness))

/-! ## 7. Per-location (disjunctive) ranking — the sound granularity

Checking each self-loop *individually* is unsound: two self-loops at one location,
each with its own ranking function, can interleave into a non-terminating run
(`x'=x-1,y'=y+1` and `x'=x+1,y'=y-1`). The fix, matching
`SelfLoopTermination.selfloops_to_ip`, is to certify **all** self-loops at a
location *jointly*: find a **single** linear ranking function `r` that decreases on
every self-loop at that location. The SMT query below gives each self-loop `i` its
own multipliers/conditions (1a)–(1d) and forces the derived `rᵢ := λ₂ᵢ·A'ᵢ` to be
equal across all `i`. -/

/-- All self-loops at location `l` (the edges of `selfloops_to_ip l`). -/
def IntegerProgram.selfLoopsAt (ip : IntegerProgram) (l : Nat) : List Transition :=
  ip.edges.filter (fun t => t.src == l && t.tgt == l)

/-- The distinct locations that carry at least one self-loop. -/
def IntegerProgram.selfLoopLocations (ip : IntegerProgram) : List Nat :=
  ip.selfLoopEdges.foldl (fun acc t => if acc.contains t.src then acc else acc ++ [t.src]) []

/-- Disjunctive Farkas query for the self-loops `rowsList` at one location, over a
    shared `n` variables. `sat` ⟺ a single linear ranking function decreases on
    every self-loop, soundly ruling out non-terminating interleavings. -/
def locationFarkasQuery (rowsList : List (List Row)) (n : Nat) : String :=
  let indexed := rowsList.zip (List.range rowsList.length)
  let llam1 : Nat → Nat → String := fun i r => s!"l1_{i}_{r}"
  let llam2 : Nat → Nat → String := fun i r => s!"l2_{i}_{r}"
  -- ∑ᵣ coeff(rowᵣ) · λ(i,r) over the rows of self-loop `i`, dropping zeros
  let sumT : List Row → Nat → (Nat → Nat → String) → (Row → Int) → String :=
    fun rows i lamName coeff =>
      smtSum ((rows.zip (List.range rows.length)).filterMap (fun (r, ridx) =>
        let c := coeff r
        if c == 0 then none else some s!"(* {intSMT c} {lamName i ridx})"))
  let decls := indexed.flatMap (fun (rows, i) =>
    (List.range rows.length).map (fun r =>
      s!"(declare-const {llam1 i r} Real)\n(declare-const {llam2 i r} Real)"))
  let nonneg := indexed.flatMap (fun (rows, i) =>
    (List.range rows.length).map (fun r =>
      s!"(assert (>= {llam1 i r} 0))\n(assert (>= {llam2 i r} 0))"))
  -- (1a)–(1d) per self-loop `i`
  let conds := indexed.flatMap (fun (rows, i) =>
    (List.range n).map (fun j =>
      s!"(assert (= {sumT rows i llam1 (·.a'Coeff j)} 0))") ++
    (List.range n).map (fun j =>
      s!"(assert (= (- {sumT rows i llam1 (·.aCoeff j)} {sumT rows i llam2 (·.aCoeff j)}) 0))") ++
    (List.range n).map (fun j =>
      s!"(assert (= {sumT rows i llam2 (fun r => r.aCoeff j + r.a'Coeff j)} 0))") ++
    [s!"(assert (< {sumT rows i llam2 (·.b)} 0))"])
  -- shared ranking function: rᵢ = r₀ for every i ≥ 1, column by column
  let shared := match indexed with
    | [] => []
    | (rows0, _) :: rest =>
        rest.flatMap (fun (rows, i) =>
          (List.range n).map (fun j =>
            s!"(assert (= {sumT rows i llam2 (·.a'Coeff j)} {sumT rows0 0 llam2 (·.a'Coeff j)}))"))
  String.intercalate "\n"
    (["(set-logic QF_LRA)", ""] ++ decls ++ [""] ++ nonneg ++ [""]
      ++ conds ++ [""] ++ shared ++ ["", "(check-sat)"])

/-- Build the disjunctive query for location `l` together with the rows and shared
    variable count used, or `none` if some self-loop at `l` is unsupported. -/
def IntegerProgram.locationSMT (ip : IntegerProgram) (l : Nat) :
    Option (String × List (List Row) × Nat) := do
  let loops := ip.selfLoopsAt l
  let n := loops.foldl (fun acc t => max acc t.numVars) 0
  let rowsList ← loops.mapM (fun t => t.toRowsN n)
  some (locationFarkasQuery rowsList n, rowsList, n)

/-- Certificate for self-loop index `ti` at a location, reading `l1_ti_r`/`l2_ti_r`
    from the model (defaulting to `0` if absent). -/
def FarkasCert.ofModelIdx (rows : List Row) (n ti : Nat)
    (model : List (String × Rat)) : FarkasCert :=
  let m := rows.length
  let get (name : String) : Rat :=
    (model.find? (fun p => p.1 == name)).map (·.2) |>.getD 0
  { rows := rows, n := n,
    lam1 := (List.range m).map (fun r => get s!"l1_{ti}_{r}"),
    lam2 := (List.range m).map (fun r => get s!"l2_{ti}_{r}") }

/-- A verified joint certificate for a location: one checked `FarkasCert` per
    self-loop, all sharing a single ranking function. -/
structure LocationCert where
  loc   : Nat
  n     : Nat
  certs : List FarkasCert
deriving Repr

/-- Every per-self-loop certificate satisfies (1a)–(1d), and all share one ranking
    function `r := λ₂·A'`. This is the executable analogue of a Farkas witness for
    `selfloops_to_ip loc`. -/
def LocationCert.check (lc : LocationCert) : Bool :=
  lc.certs.all FarkasCert.check
    && (match lc.certs with
        | []         => true
        | c0 :: rest => rest.all (fun c =>
            (List.range lc.n).all (fun j =>
              (c.rankingCoeff j - c0.rankingCoeff j).num == 0)))

/-- The shared ranking function and each self-loop's strict-decrease amount. -/
def LocationCert.rankingString (lc : LocationCert) : String :=
  match lc.certs with
  | []      => "r(x) = 0   (no self-loops)"
  | c0 :: _ =>
      let terms := (List.range lc.n).filterMap (fun j =>
        let rj := c0.rankingCoeff j
        if rj.num == 0 then none else some s!"({rj})·x{j}")
      let body := if terms.isEmpty then "0" else String.intercalate " + " terms
      let deltas := String.intercalate ", " (lc.certs.map (fun c => toString c.delta))
      s!"r(x) = {body}   (shared; per-loop δ = {deltas})"

/-- Outcome of the joint synthesize-and-verify step for one location. -/
inductive LocCheck where
  | noLoops                              -- no self-loops at this location
  | unsupported                          -- some self-loop has an unsupported guard
  | noRank                               -- Z3: unsat — no shared ranking function
  | unknown                              -- Z3: unknown
  | verified        (cert : LocationCert)
  | modelUnverified (cert : LocationCert)
  | solverError     (msg : String)
deriving Repr

/-- `true` only when a joint certificate was produced *and* independently verified
    (or the location has no self-loops, which is trivially fine). -/
def LocCheck.isVerified : LocCheck → Bool/plan
  | .verified _ => true
  | .noLoops    => true
  | _           => false

/-- **Sound pipeline core.** For location `l`, ask Z3 for a single ranking function
    covering *all* its self-loops, then read the model back and re-verify. -/
def IntegerProgram.checkSelfLoopLocation (ip : IntegerProgram) (l : Nat) : IO LocCheck := do
  if (ip.selfLoopsAt l).isEmpty then pure .noLoops
  else match ip.locationSMT l with
    | none => pure .unsupported
    | some (query, rowsList, n) => do
        let smt := "(set-option :produce-models true)\n" ++ query ++ "\n(get-model)"
        let (res, model) ← runZ3WithModel smt
        match res with
        | .unsat   => pure .noRank
        | .unknown => pure .unknown
        | .error m => pure (.solverError m)
        | .sat     =>
            let certs := (rowsList.zip (List.range rowsList.length)).map
              (fun (rows, ti) => FarkasCert.ofModelIdx rows n ti model)
            let lc : LocationCert := { loc := l, n := n, certs := certs }
            pure (if lc.check then .verified lc else .modelUnverified lc)

/-- For every location carrying self-loops, jointly synthesize and verify a single
    ranking function. This is the sound replacement for `checkSelfLoopsWitness`. -/
def IntegerProgram.checkSelfLoopLocationsWitness (ip : IntegerProgram) :
    IO (List (Nat × LocCheck)) :=
  ip.selfLoopLocations.mapM (fun l => do pure (l, ← ip.checkSelfLoopLocation l))
