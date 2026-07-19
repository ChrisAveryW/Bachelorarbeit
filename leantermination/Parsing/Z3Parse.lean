import Std

set_option linter.unusedVariables false

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

/-- Represents the S-Expression-Model of Z3. -/
inductive Z3_expr where
  | atom : String → Z3_expr
  | node : List Z3_expr → Z3_expr
deriving Repr, Inhabited

/-- split and refine not expr chars -/
private def tokenize (s : String) : List String :=
  let spaced := s.replace "(" " ( " |>.replace ")" " ) "
                 |>.replace "\n" " " |>.replace "\t" " " |>.replace "\r" " "
  (spaced.splitOn " ").filter (· ≠ "")

private partial def parseZ3_exprs : List String → List Z3_expr × List String
  | [] => ([], [])
  | ")" :: rest => ([], ")" :: rest)
  | "(" :: rest =>
      let (inner, rest1) := parseZ3_exprs rest
      let (siblings, rest2) := parseZ3_exprs (rest1.drop 1)
      (Z3_expr.node inner :: siblings, rest2)
  | tok :: rest =>
      let (siblings, rest1) := parseZ3_exprs rest
      (Z3_expr.atom tok :: siblings, rest1)

private def parseForest (toks : List String) : List Z3_expr := (parseZ3_exprs toks).1

-- pattern match function definitions
private partial def Z3_expr.collectDefs : Z3_expr → List (String × Z3_expr)
  | .atom _ => []
  | .node children =>
      let here := match children with
        | (.atom "define-fun") :: (.atom name) :: _ :: _ :: body :: _ => [(name, body)]
        | _ => []
      here ++ children.flatMap Z3_expr.collectDefs

-- parse to rational number
private def parseRatAtom (s : String) : Option Rat :=
  match s.splitOn "." with
  | [_]    => s.toInt?.map Rat.ofInt
  | [i, f] =>
      let neg   := i.startsWith "-"
      let iCore := if neg then i.drop 1 else i
      let iVal  := if iCore.isEmpty then some 0 else iCore.toNat?
      let fVal  := if f.isEmpty then some 0 else f.toNat?
      match iVal, fVal with
      | some iv, some fv =>
          let scale : Nat := 10 ^ f.length
          let num   : Int := (iv : Int) * (scale : Int) + (fv : Int)
          let q := mkRat num scale
          some (if neg then -q else q)
      | _, _ => none
  | _ => none

-- evaluate expression to rational value
private partial def evalRatZ3_expr : Z3_expr → Option Rat
  | .atom a               => parseRatAtom a
  | .node [.atom "-", x]    => (evalRatZ3_expr x).map (fun r => -r)
  | .node [.atom "-", x, y] => do return (← evalRatZ3_expr x) - (← evalRatZ3_expr y)
  | .node [.atom "+", x, y] => do return (← evalRatZ3_expr x) + (← evalRatZ3_expr y)
  | .node [.atom "*", x, y] => do return (← evalRatZ3_expr x) * (← evalRatZ3_expr y)
  | .node [.atom "/", x, y] => do return (← evalRatZ3_expr x) / (← evalRatZ3_expr y)
  | .node [x]               => evalRatZ3_expr x
  | _                       => none

/-- Parse a full Z3-(get-model) reply into name ↦ Rat binding. -/
def parseModel (out : String) : List (String × Rat) :=
  (parseForest (tokenize out)).flatMap Z3_expr.collectDefs
    |>.filterMap (fun (name, body) => (evalRatZ3_expr body).map (fun r => (name, r)))
