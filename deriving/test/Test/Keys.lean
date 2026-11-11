/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import JsonDeriving
import Test.Runner

open Json

namespace Test.Keys

@[json_keys snake_case]
structure Snake where
  whyNone : String
  perOption : Array Nat
  gPerMol? : Option Nat
  url : String
deriving ToJson, FromJson, BEq, Repr

@[json_keys snake_case (notKnown := "notKnown") (bondedTo := "bonds")]
structure Mixed where
  notKnown : Nat
  bondedTo : Nat
  restsOn : Nat
deriving ToJson, FromJson, BEq, Repr

@[json_keys (second := "two")]
structure Only where
  first : Nat
  second : Nat
deriving ToJson, FromJson, BEq, Repr

structure Plain where
  whyNone : Nat
deriving ToJson, FromJson, BEq, Repr

/-- error: cannot derive a JSON codec for Test.Keys.Clash: the fields oneTwo and one_two would both be written as "one_two" -/
#guard_msgs in
@[json_keys snake_case]
structure Clash where
  oneTwo : Nat
  one_two : Nat
deriving ToJson

/-- error: Test.Keys.Missing has no field nope -/
#guard_msgs in
@[json_keys (nope := "x")]
structure Missing where
  here : Nat

private def encodesTo [ToJson α] (name : String) (v : α) (expected : String) : TestCase where
  name := name
  run :=
    let got := compress (toJson v)
    if got == expected then pure () else throw (IO.userError s!"encoded as {got}")

private def roundTrips [ToJson α] [FromJson α] [BEq α] [Repr α] (name : String) (v : α) :
    TestCase where
  name := name
  run :=
    match Json.parse (compress (toJson v)) with
    | .error e => throw (IO.userError s!"the text did not parse: {e}")
    | .ok j =>
      match fromJson? j with
      | .ok (w : α) => if w == v then pure () else throw (IO.userError s!"came back as {repr w}")
      | .error e => throw (IO.userError s!"failed to decode: {e}")

private def refuses (name : String) (α : Type) [FromJson α] (text : String) : TestCase where
  name := name
  run :=
    match Json.parse text with
    | .error e => throw (IO.userError s!"the text did not parse: {e}")
    | .ok j =>
      match fromJson? (α := α) j with
      | .error _ => pure ()
      | .ok _ => throw (IO.userError "accepted")

private def snake : Snake := { whyNone := "w", perOption := #[1], gPerMol? := some 2, url := "u" }
private def snakeText : String :=
  "{\"why_none\":\"w\",\"per_option\":[1],\"g_per_mol\":2,\"url\":\"u\"}"

def all : Array TestCase := #[
  encodesTo "snake_case renames every field, in field order" snake snakeText,
  encodesTo "an absent optional field is still left out"
    { snake with gPerMol? := none } "{\"why_none\":\"w\",\"per_option\":[1],\"url\":\"u\"}",
  encodesTo "an override beats the convention, and the rest follow it"
    ({ notKnown := 1, bondedTo := 2, restsOn := 3 : Mixed })
    "{\"notKnown\":1,\"bonds\":2,\"rests_on\":3}",
  encodesTo "an override without a convention leaves the other names as they are"
    ({ first := 1, second := 2 : Only }) "{\"first\":1,\"two\":2}",
  encodesTo "no configuration keeps the field names" ({ whyNone := 1 : Plain }) "{\"whyNone\":1}",
  roundTrips "a renamed structure" snake,
  roundTrips "a renamed structure with an optional field absent" { snake with gPerMol? := none },
  roundTrips "a structure with overrides" ({ notKnown := 1, bondedTo := 2, restsOn := 3 : Mixed }),
  roundTrips "an unconfigured structure" ({ whyNone := 1 : Plain }),
  refuses "the Lean name is not accepted under snake_case" Snake
    "{\"whyNone\":\"w\",\"perOption\":[1],\"gPerMol\":2,\"url\":\"u\"}",
  refuses "the convention's name is not accepted where an override replaced it" Mixed
    "{\"bondedTo\":2,\"notKnown\":1,\"rests_on\":3}",
  refuses "the renamed key is not accepted where nothing renames" Plain "{\"why_none\":1}"
]

end Test.Keys
