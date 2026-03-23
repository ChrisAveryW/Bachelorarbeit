import Mathlib


-- Definition of Integer Programs

-- Definition of Polynomials
-- Expr.lit 5 refers to the integer value 5. Expr.var 5 refers to the variable x₅.
-- A variable stream of x₀, x₁, x₂, ... is assumed (there are no other variables, like y, z,...)
inductive Expr where
  | lit  : Int → Expr
  | var  : Nat → Expr
  | add  : Expr → Expr → Expr
  | sub  : Expr → Expr → Expr
  | pow  : Expr → Nat → Expr
  | mul  : Expr → Expr → Expr
deriving Repr, DecidableEq

-- Definition of States
-- these provide Expr.var's with values.
-- e.g. Env.vars[0] correspond to the value of x₀.
structure Env where
  vars : List Int
deriving Repr, DecidableEq

-- Evaluation of Expression
-- The evaluation always works with a provided state
-- TODO: currently an invalid matching between State and Expression could is handeld through a
--       quick fix: by defining all values that don't match to -1. This should be replaced by an invariant or Option Type
def Expr.eval (expr : Expr) (env : Env) : Int :=
  match expr with
  | .lit n => n
  | .var n => env.vars.getD n (-1)
  | .add a b => (Expr.eval a env ) + (Expr.eval b env)
  | .sub a b => (Expr.eval a env) - (Expr.eval b env)
  | .pow b e => (Expr.eval b env)^e
  | .mul a b => (Expr.eval a env) * (Expr.eval b env)


-- Definition of Constraints
-- Constraints are either take two Expressions and create a Constraint or they take arbitrary constraints
-- and create new constraints inductivley. The base cases are .tr = True and .fls = False
inductive Constraint where
  | eq  : Expr → Expr → Constraint
  | lt  : Expr → Expr → Constraint
  | gt  : Expr → Expr → Constraint
  | leq : Expr → Expr → Constraint
  | geq : Expr → Expr → Constraint
  | tr  : Constraint
  | fls : Constraint
  | not : Constraint → Constraint
  | and : Constraint → Constraint → Constraint
  | or  : Constraint → Constraint → Constraint
  | impl: Constraint → Constraint → Constraint
deriving Repr, DecidableEq

-- Definition of Constraint Evaluation
-- Constraints are evaluatad by providing states.
def Constraint.eval (c : Constraint) (env : Env) : Bool :=
  match c with
  | .eq e1 e2 => (Expr.eval e1 env) == (Expr.eval e2 env)
  | .lt e1 e2 => (Expr.eval e1 env) < (Expr.eval e2 env)
  | .leq e1 e2 => (Expr.eval e1 env) ≤ (Expr.eval e2 env)
  | .gt e1 e2 => (Expr.eval e1 env) > (Expr.eval e2 env)
  | .geq e1 e2 => (Expr.eval e1 env) ≥ (Expr.eval e2 env)
  | .tr => true
  | .fls => false
  | .not c => !(Constraint.eval c env)
  | .and c1 c2 => (Constraint.eval c1 env) ∧ (Constraint.eval c2 env)
  | .or c1 c2 => (Constraint.eval c1 env) ∨ (Constraint.eval c2 env)
  | .impl c1 c2 => (Constraint.eval c1 env) → (Constraint.eval c2 env)


-- Definition of Update function
-- The definition holds a variable (pv) and an expression to which the pv is updated to.
structure Update where
  pv : Nat
  expr : Expr
deriving Repr, DecidableEq

-- Returns the new state, which was effected by the update function.
def Update.apply (u : Update) (env : Env) : Env :=
  let newVal := Expr.eval u.expr env
  {vars := env.vars.set u.pv newVal}

-- Returns a new state, in which a list of updates was performed.
-- This is useful since, a transition can have various update functions (e.g. for various variables)
def Update.all (u : List Update) (env : Env) : Env :=
  u.foldl (fun e u => Update.apply u e) env

-- Definition of Transitions
structure Transition where
  src : Nat -- l
  tgt : Nat -- l'
  guard : Constraint
  update : List Update
deriving Repr, DecidableEq

-- Returns a tuple which describes if a transition was possible to perform,
-- given the constraint of a guard and state.
-- I chose to add the a variable determining if the transition was successful,
-- instead of just returning the same state to prevent errors in termination proofs.
-- TODO: maybe use Options, which could be cleaner
def Transition.perform (t : Transition) (env : Env) : (Bool × Env) :=
  if Constraint.eval t.guard env then
    (true, t.update.foldl (fun e u => Update.apply u e) env)
  else
    (false, env)


-- Definition of Integer Programs
-- This definition is very near to the definition of the paper.
-- There is a list of locations, which can be considered as a list l₀, l₁, l₂, ...
-- The initial location is l₀.
-- There is a list of edges, are represented by transitions.
-- There are four invariant constraints:
-- 1. h_strt = the initial location is fixed. Mainly to prevent errors later on.
-- 2. h_locs = the initial location is in the list of locations.
-- 3. h_trans = the transitions are defined on locations of this integer program.
-- 4. h_incom = the initial location doesn't have any incoming edges (constraint in paper)
structure IntegerProgram where
  locs : List Nat
  l₀ : Nat
  edges : List Transition
  h_strt : l₀ = 0
  h_locs : l₀ ∈ locs
  h_trans : ∀ t ∈ edges, t.src ∈ locs ∧ t.tgt ∈ locs
  h_incom : ¬∃ t ∈ edges, t.tgt = l₀
deriving Repr, DecidableEq


-- Functions for Ineger Programs
-- currently not in usage
def IntegerProgram.avail_trans (ip : IntegerProgram) (loc : Nat) : List Transition :=
  ip.edges.filter (fun tr => tr.src == loc)

def IntegerProgram.succs (ip : IntegerProgram) (loc : Nat) : List Nat :=
  (ip.edges.filter (fun tr => tr.src == loc)).map (fun tr => tr.tgt)



-- Definition of Configuration
-- A Configuration is the combination of a location with a state (Loc × State)
-- (This is always regarding an Integer Program.)
structure Configuration where
  loc : Nat
  env : Env
  prog: IntegerProgram
deriving Repr, DecidableEq

-- Definition of an empty Configuration, which is sometimes useful.
def empty_configuration : Configuration :=
  {loc := 0, env := {vars := []}, prog:=
  {locs := [0], l₀ := 0, edges := [],
   h_strt := by decide,
   h_locs := by decide,
   h_trans := by decide,
   h_incom := by decide}}

-- Definition of some functions on Configurations
-- They are not in usage currently
def Configuration.env_avail_trans (ip : IntegerProgram) (loc : Nat) (env : Env) : List Transition :=
  ip.edges.filter (fun tr => tr.src == loc && Constraint.eval tr.guard env)

def Configuration.env_succs (ip : IntegerProgram) (loc : Nat) (env : Env) : List Nat :=
  (ip.edges.filter (fun tr => tr.src == loc && Constraint.eval tr.guard env)).map (fun tr => tr.tgt)

-- Definition of a Natural Number with Infinity
-- Not in usage, using Mathlib for this functionality: ℕ∞
inductive ExtNat where
  | fin : Nat → ExtNat
  | inf : ExtNat
deriving Repr

-- Definition of order for the Natural Numbers with Infinity
def ExtNat.max : ExtNat → ExtNat → ExtNat
  | .inf, _ => .inf
  | _, .inf => .inf
  | .fin a, .fin b => .fin (Nat.max a b)

-- Calculation of Configuration Step
-- Returns the next configuration, if you perform a valid transition.
-- Here in the case of a step, which doesn't make sense an empty_configuration is returned.
-- TODO: replace the empty_configuration with invariant or Option.
def Configuration.step_computation (c : Configuration) (t : Transition) : Configuration :=
  if t ∈ c.prog.edges && t.src == c.loc then
    let res := (Transition.perform t c.env)
    if res.1 then
      {loc := t.tgt, env := res.2, prog := c.prog}
    else
      empty_configuration
  else
    empty_configuration

-- Definition of Configuration Step
-- This definition is used for proofs not for algorithmic functions.
-- does (lₜ,σ) → (lₜ',σ') hold with transition t=(lₜ, τ, η, l'ₜ)
def Configuration.step (c1 : Configuration) (c2 : Configuration) : Prop :=
  (c1.prog = c2.prog) ∧ -- c1,c2 are definied on the same Integer Program
  ∃ t ∈ c1.prog.edges,
    (Constraint.eval t.guard c1.env) ∧ -- σ(τ) = true
  (c2.env = Update.all t.update c1.env) ∧ -- v ∈ PV we have σ(η(v)) = σ'(v)
  (t.src = c1.loc ∧ t.tgt = c2.loc)-- l = lₜ and l' = l'ₜ


-- Definition of Paths
-- This definition represents "is there a path of the length n, which starts in a and ends in b" (a, b are Configurations)
-- expressed differently: does (l,σ) →ᵏ (l',σ') hold for a specific k ∈ ℕ
def Configuration.pathN : Nat → Configuration → Configuration →  Prop
    | 0,    _, _ => False
    | n + 1,c1, c2 => Configuration.step c1 c2 ∨
              ∃ ci : Configuration, Configuration.step c1 ci ∧ Configuration.pathN n ci c2

-- Definition of Paths
-- This is the reduced definition of paths, without having to provide the length
-- "is there a path of which starts in a and ends in b, while a and b are configurations"
-- expressed differently: does (l,σ) →ᵏ (l',σ') hold, while k ∈ ℕ
def Configuration.path (c1 c2 : Configuration) : Prop :=
  ∃ n : Nat, Configuration.pathN n c1 c2


-- Defining set of execution lengths
def Configuration.all_succ_lengths (c1 : Configuration) : Set ℕ∞ :=
  {k : ℕ∞ | ∃ (n : ℕ) (c : Configuration), k = n ∧ Configuration.pathN n c1 c}

-- Defining rc: supremum of set of all lengths
-- rc(σ) = sup { k ∈ ℕ | (l₀, σ) →ᵏ (_, _)}
noncomputable def Configuration.rc (c1 : Configuration) : ℕ∞:=
  sSup (Configuration.all_succ_lengths c1)


-- Definition of a Path
-- This is doesn't include Configurations, just if there is a path, regardless of states and guards.
def IntegerProgram.pathN : Nat → Nat → Nat → IntegerProgram → Prop
  | 0, _, _, _ => false
  --| 1, l1, l2, ip => ∃ t ∈ ip.edges, t.src = l1 ∧ t.tgt = l2
  | n+1, l1, l2, ip => (∃ t ∈ ip.edges, t.src = l1 ∧ t.tgt = l2)
  ∨ (∃ t ∈ ip.edges, t.src = l1 ∧ IntegerProgram.pathN n t.tgt l2 ip)

-- TODO: more precise definition, but breaks some proofs, integrate later!
--def IntegerProgram.pathN : Nat → Nat → Nat → IntegerProgram → Prop
--  | 0, _, _, _ => false
--  | 1, l1, l2, ip => ∃ t ∈ ip.edges, t.src = l1 ∧ t.tgt = l2
--  | n+1, l1, l2, ip => ∃ t ∈ ip.edges, t.src = l1 ∧ IntegerProgram.pathN n t.tgt l2 ip


-- Definition of Locations which are seen in path
-- REMARKS: this could be undecidable, should not be used.
-- TODO: transform to be defined differently
def IntegerProgram.pathLocs : ∀ (n : ℕ) (l1 l2 : ℕ) (p : IntegerProgram),
    IntegerProgram.pathN n l1 l2 p → List ℕ
  | 0, _, _, _, _ => []
  | 1, l1, l2, _, _=> [l1, l2]
  | n+2, l1, l2, ip, h => by
    --let ⟨t, _, _, h_next⟩ := h
    --l1 :: IntegerProgram.pathLocs (n+1) t.tgt l2 ip h_next
    sorry

-- Definition of Path
-- this is analog to the reduced definition of Paths with Configurations
-- It definies paths along Integer Programs without regarding guards or states
def IntegerProgram.path (l1 l2 : Nat) (ip : IntegerProgram) : Prop  :=
  ∃ n : Nat, IntegerProgram.pathN n l1 l2 ip


-- Definition of an acyclic Integer Program
def IntegerProgram.acyclic (p : IntegerProgram) : Prop :=
  ∀ x ∈ p.locs, ¬(IntegerProgram.path x x p)


-- Example of an Integer Programs


-- Knoten l₀, l₂ (starting location: l₀)
-- Variables x₀, x₁
-- Transition #1 (l₀, (x₀ > 0 ∨ x₁ < 0), [η(x₀)= x₀-1, η(x₁) = x₀-x₁], l₂)
-- Transition #2 (l₂, (x₁ = 0), [η(x₁) = 1], l₂)
-- State x₀ := 1, x₁ := 0

def upd1_1 : Update :=
  {pv := 0, expr := Expr.sub (Expr.var 0) (Expr.lit 1)}
def upd1_2 : Update :=
  {pv := 1, expr := Expr.sub (Expr.var 0) (Expr.var 1)}

def trans_1 : Transition :=
  {src := 0,
   tgt := 2,
   guard := Constraint.or (
    Constraint.gt (Expr.var 0) (Expr.lit 0)) (Constraint.lt (Expr.var 1) (Expr.lit 0)),
   update := [upd1_1, upd1_2]}

def trans_2 : Transition :=
  {src := 2,
   tgt := 2,
   guard := Constraint.eq (Expr.var 0) (Expr.lit 0),
   update := [{pv := 1, expr := Expr.lit 1}]}

def example_program : IntegerProgram :=
  {locs := [0, 2],
   l₀ := 0,
   edges := [trans_1, trans_2],
   h_strt := by decide,
   h_locs := by decide,
   h_trans := by decide,
   h_incom := by decide}
