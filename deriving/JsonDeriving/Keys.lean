/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Attributes
public meta import Lean.Structure
public meta import Lean.Elab.Command

public section

namespace Json.Deriving

open Lean

/-- A naming convention for the JSON keys of a structure's fields. -/
meta inductive KeyCase where
  /-- `whyNone` is written `why_none`. -/
  | snake_case
  /-- `whyNone` is written `WHY_NONE`. -/
  | SCREAMING_SNAKE_CASE
  /-- `whyNone` is written `why-none`. -/
  | kebab_case
  /-- `why_none` is written `whyNone`. -/
  | camelCase
deriving Inhabited, BEq

/-- A naming convention, written as its own name. -/
syntax jsonCase := &"snake_case" <|> &"SCREAMING_SNAKE_CASE" <|> &"camelCase" <|>
  (&"kebab" noWs "-" noWs "case")

/--
The words of a name: split at `_`, and before a capital that follows a lower case letter or a
digit, or that begins a word after a run of capitals (`parseURLText` is `parse`, `URL`, `Text`).
-/
meta def KeyCase.words (s : String) : List String :=
  let cs := s.toList
  let (done, current) := cs.zipIdx.foldl (init := (#[], "")) fun (done, current) (c, i) =>
    if c == '_' then (done.push current, "") else
      let prev? := if i == 0 then none else cs[i - 1]?
      let next? := cs[i + 1]?
      let boundary := c.isUpper && !current.isEmpty &&
        (prev?.any Char.isLower || prev?.any Char.isDigit ||
          (prev?.any Char.isUpper && next?.any Char.isLower))
      if boundary then (done.push current, c.toString) else (done, current.push c)
  (done.push current).toList

private meta def capitalise (w : String) : String :=
  match w.toList with
  | c :: cs => String.ofList (c.toUpper :: cs.map Char.toLower)
  | [] => ""

/--
A name under the convention; a run of capitals such as `URL` is one word. `camelCase` ignores empty
words, so that `_x` is `x` and `x_` is `x`; a name with no letters at all, such as `_`, gives `""`.
-/
meta def KeyCase.apply (convention : KeyCase) (s : String) : String :=
  let words := KeyCase.words s
  match convention with
  | .snake_case => "_".intercalate (words.map String.toLower)
  | .SCREAMING_SNAKE_CASE => "_".intercalate (words.map String.toUpper)
  | .kebab_case => "-".intercalate (words.map String.toLower)
  | .camelCase =>
    match words.filter (!·.isEmpty) with
    | first :: rest => String.join (first.toLower :: rest.map capitalise)
    | [] => ""

meta def KeyCase.ofSyntax (stx : Syntax) : KeyCase :=
  match stx.getHead?.map (·.getAtomVal) with
  | some "SCREAMING_SNAKE_CASE" => .SCREAMING_SNAKE_CASE
  | some "camelCase" => .camelCase
  | some "kebab" => .kebab_case
  | _ => .snake_case

/-- How the derived codecs of a structure name its fields in JSON. -/
meta structure KeyNaming where
  convention : Option KeyCase := none
  /-- Lean field name and the whole of its key, which no convention applies to. -/
  overrides : Array (Name × String) := #[]
deriving Inhabited

/-- The key of a field named `s`: its override, else the convention's. -/
meta def KeyNaming.apply (naming : KeyNaming) (n : Name) (s : String) : String :=
  match naming.overrides.find? (·.1 == n) with
  | some (_, key) => key
  | none =>
    match naming.convention with
    | some convention => convention.apply s
    | none => s

/--
`@[json_keys snake_case (whyNone := "why_none")]` on a structure names the keys of its derived
`ToJson` and `FromJson`: by a convention, with the listed fields overriding it. Both parts are
optional. A field keeps its name, minus any trailing `?`, where neither applies.
-/
syntax (name := jsonKeys) "json_keys" (ppSpace jsonCase)?
  (ppSpace "(" ident " := " str ")")* : attr

/-- The convention and overrides of the attribute, checking each name with `known`. -/
private meta def parseNaming (stx : Syntax) (noun what : String) (known : Name → Bool) :
    AttrM KeyNaming := do
  let convention := if stx[1].isNone then none else some (KeyCase.ofSyntax stx[1][0])
  let mut overrides := #[]
  for pair in stx[2].getArgs do
    let n := pair[1].getId
    unless known n do
      throwErrorAt pair[1] "{what} {n}"
    if overrides.any (·.1 == n) then
      throwErrorAt pair[1] "the {noun} of {n} is given twice"
    overrides := overrides.push (n, pair[3].isStrLit?.getD "")
  return { convention, overrides }

private meta initialize keyNamingAttr : ParametricAttribute KeyNaming ←
  registerParametricAttribute {
    name := `jsonKeys
    descr := "the JSON keys of a structure's derived codecs"
    getParam := fun declName stx => do
      unless isStructure (← getEnv) declName do
        throwError "json_keys applies to structures, and {declName} is not one"
      let fields := getStructureFields (← getEnv) declName
      parseNaming stx "key" s!"{declName} has no field" fields.contains
  }

/-- The keys a structure's derived codecs use, which are as given by `json_keys` if present. -/
meta def keyNaming (env : Environment) (structName : Name) : KeyNaming :=
  (keyNamingAttr.getParam? env structName).getD {}

end Json.Deriving
