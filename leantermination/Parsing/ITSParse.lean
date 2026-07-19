import leantermination.Parsing.Preparse
import leantermination.Datastructures.IntegerProgram
import Mathlib.Tactic.Tauto

/-!
Builds a parsed IntegerProgram from preparsed ITS files.
-/

set_option linter.style.longLine false

def buildVarMap (srcArgs : List String) : Std.HashMap String Nat :=
  let indices := List.range srcArgs.length
  (srcArgs.zip indices).foldl (fun map (name, i) => map.insert name i) {}

def buildLocMap (locations : List String) : Std.HashMap String Nat :=
  let indices := List.range locations.length
  (locations.zip indices).foldl (fun map (name, i) => map.insert name i) {}

-- translate ParsedExpr to Expr
partial def ParsedExpr.toExpr (e : ParsedExpr) (varMap : Std.HashMap String Nat) : Option Expr :=
  match e with
  | .lit n   => some (Expr.lit n)
  | .var s   => varMap.get? s |>.map Expr.var
  | .app "+" args => do
      match args with
      | []         => pure (Expr.lit 0)
      | [a]        => a.toExpr varMap
      | a :: rest  => pure (Expr.add (← a.toExpr varMap) (← (ParsedExpr.app "+" rest).toExpr varMap))
  | .app "-" args => do
      match args with
      | []         => pure (Expr.lit 0)
      | [a]        => pure (Expr.sub (Expr.lit 0) (← a.toExpr varMap))  -- unary minus
      | a :: rest  => pure (Expr.sub (← a.toExpr varMap) (← (ParsedExpr.app "+" rest).toExpr varMap))
  | .app "*" args => do
      match args with
      | []         => pure (Expr.lit 1)
      | [a]        => a.toExpr varMap
      | a :: rest  => pure (Expr.mul (← a.toExpr varMap) (← (ParsedExpr.app "*" rest).toExpr varMap))
  | _ => none

-- translate ParsedExpr to Constraint
partial def ParsedExpr.toConstraint (e : ParsedExpr) (varMap : Std.HashMap String Nat) : Option Constraint :=
  --dbg_trace s!"tc1"
  --dbg_trace s!"tc2: {reprStr e}"
  match e with
  | .app "and" args => do
      match args with
      | []        => pure Constraint.true
      | [a]       => a.toConstraint varMap
      | a :: rest => pure (Constraint.and (← a.toConstraint varMap) (← (ParsedExpr.app "and" rest).toConstraint varMap))
  | .app "or" args => do
      match args with
      | []        => pure Constraint.false
      | [a]       => a.toConstraint varMap
      | a :: rest => pure (Constraint.or (← a.toConstraint varMap) (← (ParsedExpr.app "or" rest).toConstraint varMap))
  | .app "not" [a] => do
      pure (Constraint.not (← a.toConstraint varMap))
  -- atomic comparisons using Cmp
  | .app "=" [a, b] => do
      pure (Constraint.atom .eq (← a.toExpr varMap) (← b.toExpr varMap))
  | .app "==" [a, b] => do
      pure (Constraint.atom .eq (← a.toExpr varMap) (← b.toExpr varMap))
  | .app "<" [a, b] => do
      pure (Constraint.atom .lt (← a.toExpr varMap) (← b.toExpr varMap))
  -- derived comparisons: translated into not/and/atom combinations
  | .app ">" [a, b] => do
      pure (Constraint.gt (← a.toExpr varMap) (← b.toExpr varMap))
  | .app ">=" [a, b] => do
      pure (Constraint.geq (← a.toExpr varMap) (← b.toExpr varMap))
  | .app "<=" [a, b] => do
      pure (Constraint.leq (← a.toExpr varMap) (← b.toExpr varMap))
  -- distinct (a, b)  is equal to  ¬(a = b) @todo make a dedicated constraint
  | .app "distinct" [a, b] => do
      pure (Constraint.not (Constraint.atom .eq (← a.toExpr varMap) (← b.toExpr varMap)))
  | s => dbg_trace s!"toConstraint: {reprStr s}"
  none

-- translate target args to List Update
def toUpdates (srcArgs : List String) (tgtArgs : List (Option ParsedExpr))
    (varMap : Std.HashMap String Nat) : Option (List Update) :=
  let indices := List.range srcArgs.length
  let pairs := indices.zip tgtArgs
  --dbg_trace s!"u1: {indices}, {reprStr pairs}"
  pairs.mapM fun (i, maybeExpr) => do
    let e ← maybeExpr
    let expr ← e.toExpr varMap
    --dbg_trace s!"\nu2:\n{reprStr expr}\n"
    pure { pv := i, expr }

-- translate a parsedRule to Transition
def ParsedRule.toTransition (r : ParsedRule) (locMap : Std.HashMap String Nat) : Option Transition := do
  --dbg_trace "t1"
  let src ← locMap.get? r.source_location
  let tgt ← locMap.get? r.target_location
  --dbg_trace s!"src: {src} tgt: {tgt}"
  let varMap := buildVarMap r.source_args
  --dbg_trace s!"varMap: {reprStr varMap}"
  let update ← toUpdates r.source_args r.target_args varMap
  -- if no guard is present, use trivially true constraint: ¬(0 < 0)  i.e. 0 ≥ 0
  --dbg_trace s!"t2: {reprStr update}"
  let guard ← match r.guard with
    | none   => some (Constraint.not (Constraint.atom .lt (Expr.lit 0) (Expr.lit 0)))
    | some g => g.toConstraint varMap
  --dbg_trace s!"t3: {reprStr guard}"
  pure { src, tgt, guard, update }

-- translate a full ParsedITS to IntegerProgram
def ParsedITS.toIntegerProgram (its : ParsedITS) : Option IntegerProgram := do
  let locMap := buildLocMap its.locations
  let locs   := List.range its.locations.length
  let edges  ← its.rules.mapM (·.toTransition locMap)
  let l₀     ← locMap.get? its.entrypoint
  if l₀ != 0 then none
  else
    -- decide the invariant at runtime
    if h : ∀ t ∈ edges, t.src ∈ locs ∧ t.tgt ∈ locs then
      some { locs, l₀ := 0, edges, h_edges := h }
    else
      none

def parseITS (s : String) : Option IntegerProgram := do
    let preparsed ← preParseITS s
    ParsedITS.toIntegerProgram preparsed
