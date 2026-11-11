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
deriving Inhabited, BEq

/-- How the derived codecs of a structure name its fields in JSON. -/
meta structure KeyNaming where
  convention : Option KeyCase := none
  /-- Lean field name and the whole of its key, which no convention applies to. -/
  overrides : Array (Name × String) := #[]
deriving Inhabited

/--
`@[json_keys snake_case (whyNone := "why_none")]` on a structure names the keys of its derived
`ToJson` and `FromJson`: by a convention, with the listed fields overriding it. Both parts are
optional. A field keeps its name, minus any trailing `?`, where neither applies.
-/
syntax (name := jsonKeys) "json_keys" (ppSpace &"snake_case")?
  (ppSpace "(" ident " := " str ")")* : attr

/-- `whyNone` as `why_none`; a run of capitals such as `URL` stays together. -/
meta def KeyCase.apply : KeyCase → String → String
  | .snake_case, s =>
    let cs := s.toList
    let out := cs.zipIdx.foldl (init := "") fun acc (c, i) =>
      let prev? := if i == 0 then none else cs[i - 1]?
      let next? := cs[i + 1]?
      let boundary := c.isUpper && i != 0 &&
        (prev?.any Char.isLower || prev?.any Char.isDigit ||
          (prev?.any Char.isUpper && next?.any Char.isLower))
      (if boundary then acc.push '_' else acc).push c.toLower
    out

private meta initialize keyNamingAttr : ParametricAttribute KeyNaming ←
  registerParametricAttribute {
    name := `jsonKeys
    descr := "the JSON keys of a structure's derived codecs"
    getParam := fun declName stx => do
      unless isStructure (← getEnv) declName do
        throwError "json_keys applies to structures, and {declName} is not one"
      let fields := getStructureFields (← getEnv) declName
      let convention := if stx[1].isNone then none else some KeyCase.snake_case
      let mut overrides := #[]
      for pair in stx[2].getArgs do
        let field := pair[1].getId
        unless fields.contains field do
          throwErrorAt pair[1] "{declName} has no field {field}"
        if overrides.any (·.1 == field) then
          throwErrorAt pair[1] "the key of {field} is given twice"
        overrides := overrides.push (field, pair[3].isStrLit?.getD "")
      return { convention, overrides }
  }

/-- The keys a structure's derived codecs use, which are as given by `json_keys` if present. -/
meta def keyNaming (env : Environment) (structName : Name) : KeyNaming :=
  (keyNamingAttr.getParam? env structName).getD {}

end Json.Deriving
