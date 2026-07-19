/-! Parse ITS ARI-Files
Extractingphase
-/

-- parsed structures
inductive ParsedExpr where
  | var : String → ParsedExpr               -- "X1", "X2", "VAR_XY"
  | lit : Int → ParsedExpr                  -- 3, -5, 0
  | app : String → List ParsedExpr → ParsedExpr   -- (+ e1 e2), (* 3 X1 X3 VAR)
deriving Repr

-- structure to hold parsed rule information
structure ParsedRule where
  source_location : String
  source_args : List String
  target_location : String
  target_args : List (Option ParsedExpr)
  guard : Option ParsedExpr
deriving Repr

-- structure to hold entire ITS file
structure ParsedITS where
  rules : List ParsedRule
  entrypoint: String
  locations : List String
deriving Repr

-- helper functions


def topLevelParens (s : String) : List String :=
  let chars := s.toList
  let rec go (chars : List Char) (depth : Nat) (current : String) (acc : List String) : List String :=
    match chars with
    | [] => if current.trimAscii.toString != "" then acc ++ [current] else acc
    | c :: rest =>
      match c with
      | '(' => go rest (depth + 1) (current.push c) acc
      | ')' =>
        let current' := current.push c
        if depth == 1 then
          go rest 0 "" (acc ++ [current'])
        else
          go rest (depth - 1) current' acc
      | _ => go rest depth (current.push c) acc
  go chars 0 "" []

def splitByWhiteSpace (s : String) : List String :=
  ((s.split (Char.isWhitespace)).toList).map (fun s => s.toString)

def joinStringList (xs : List String) : String :=
  String.join xs

def toLower (s : String) : String :=
  s.toLower

-- parse functions


def normalizeWhitespaceAndCase (s : String) : String :=
  (joinStringList (splitByWhiteSpace s)).toLower

def parseHeader1 (s : String) : Option String :=
  if normalizeWhitespaceAndCase s == "(formatlctrs)" then some s else none

def parseHeader2 (s : String) : Option String :=
  if normalizeWhitespaceAndCase s == "(theoryints)" then some s else none

def isConcatOfIntsHelper : String → Nat → Bool
| _, 0 => false
| s, fuel+1 =>
  if s.isEmpty then true
  else if s.startsWith "int" then
    isConcatOfIntsHelper (s.drop 3).toString fuel
  else
    false

def isConcatOfInts (s : String) : Bool :=
  if s.startsWith "int" && (isConcatOfIntsHelper s s.length) then true else false

def isLocation (s : String) : Bool :=
  let cleaned := normalizeWhitespaceAndCase s
  if !(cleaned.startsWith "(fun") then false
  else if !(cleaned.endsWith "))") then false
  else
    -- delete "(fun" prefix
    let afterFun := cleaned.drop 4
    -- read name: take chars until '('
    let name := afterFun.takeWhile (· != '(')
    let afterName := afterFun.drop name.positions.length
    -- name must be non-empty and alphanumeric
    if name.isEmpty || !name.all (fun c => c.isAlphanum || c == '_') then false
    -- rest must start with "(->Int"
    else if !(afterName.startsWith "(->int") then false
    else
      -- get string in between "->Int" and the closing "))"
      let afterArrow := afterName.drop 3  -- drop "(->"
      -- strip the closing "))" from the end
      let inner := afterArrow.dropEnd 2
      -- inner has to be "Int+"
      if inner.isEmpty then false
      else
        isConcatOfInts inner.toString

def parseLocationName (s : String) : Option String :=
  if isLocation s then
    let afterFun := (s.trimAscii.toString.drop 4).trimAscii.toString
    let name := afterFun.takeWhile (fun c => !c.isWhitespace && c != '(')
    some name.toString
  else none

def parseEntrypoint (s : String) : Option String :=
  let cleaned := normalizeWhitespaceAndCase s
  if cleaned.startsWith "(entrypoint" && cleaned.endsWith ")" then
    let afterKeyword := (s.trimAscii.toString.drop 11).trimAscii.toString
    let name := afterKeyword.takeWhile (fun c => !c.isWhitespace && c != ')')
    some name.toString
  else none

def splitArgs (s : String) : List String :=
  let chars := s.trimAscii.toString.toList
  let rec go (chars : List Char) (depth : Nat) (current : String) (acc : List String) : List String :=
    match chars with
    | [] =>
        let cur := current.trimAscii.toString
        if cur.isEmpty then acc else acc ++ [cur]
    | c :: rest =>
        match c with
        | '(' => go rest (depth + 1) (current.push c) acc
        | ')' =>
            let current' := current.push c
            if depth == 1 then
              go rest 0 "" (acc ++ [current'.trimAscii.toString])
            else
              go rest (depth - 1) current' acc
        | _ =>
            if c.isWhitespace && depth == 0 then
              let cur := current.trimAscii.toString
              if cur.isEmpty then go rest 0 "" acc
              else go rest 0 "" (acc ++ [cur])
            else
              go rest depth (current.push c) acc
  go chars 0 "" []

def parseLocationCall (s : String) : Option (String × List String) := do
  let trimmed := s.trimAscii.toString
  if !trimmed.startsWith "(" || !trimmed.endsWith ")" then none
  else
    let inner := (trimmed.drop 1 |>.dropEnd 1).trimAscii.toString
    let tokens := splitArgs inner
    match tokens with
    | [] => none
    | name :: args => some (name, args)


partial def parseExpr (s : String) : Option ParsedExpr :=
  let s := s.trimAscii.toString
  if s.startsWith "(" then
    let inner := (s.drop 1).dropEnd 1
    let tokens := splitArgs inner.trimAscii.toString
    match tokens with
    | [] => none
    | head :: argTokens =>
      let args := argTokens.filterMap parseExpr
      some (.app head args)
  else
    match s.toInt? with
    | some n => some (.lit n)
    | none   => some (.var s)

def is_rule (s : String) : Option ParsedRule :=
  if !(s.trimAscii.toString.startsWith "(rule") then none
  else if !(s.trimAscii.toString.endsWith ")") then none
  else
    let _inner := (s.trimAscii.toString.drop 5).trimAscii.toString
    let rule := (_inner.dropEnd 1).toString
    -- check if there's a :guard keyword
    let guardKeyword := ":guard"
    let splitByGuard := rule.splitOn guardKeyword
    let ruleWithoutGuard := splitByGuard.getD 0 ""
    let guardPart := if splitByGuard.length > 1 then some (splitByGuard.getD 1 "") else none
    let parts := topLevelParens ruleWithoutGuard.trimAscii.toString
    match parts with
    | [] => none
    | sourcePart :: rest =>
      do
        let (srcLoc, srcArgs) ← parseLocationCall sourcePart
        match rest with
        | [] => none
        | targetPart :: _ =>
          do
            let (tgtLoc, tgtArgs) ← parseLocationCall targetPart
            let cleanGuard := guardPart.map (·.trimAscii.toString)
            let parsedGuard ← match cleanGuard with
              | none => some none
              | some g => (parseExpr g).map some
            pure { source_location := srcLoc, source_args := srcArgs,
                   target_location := tgtLoc, target_args := tgtArgs.map (fun s => parseExpr s),
                   guard := parsedGuard}


def preParseITS (s : String) : Option ParsedITS := do
    let parts := topLevelParens s
    -- prase Header 1
    let _header1 :: rest1 ← pure parts | none
    let _ ← parseHeader1 _header1
    -- parse Header 2
    let _header2 :: rest2 ← pure rest1 | none
    let _ ← parseHeader2 _header2
    -- parse Locations
    let (locations, rest3) := rest2.span (isLocation ·)
    let location_names ← locations.mapM parseLocationName
    -- parse Entrypoint
    let _entrypoint :: rest4 ← pure rest3 | none
    let entrypoint_name ← parseEntrypoint _entrypoint
    -- parse Rules
    let prules := rest4.filterMap is_rule
    pure {rules := prules, entrypoint := entrypoint_name, locations := location_names}
