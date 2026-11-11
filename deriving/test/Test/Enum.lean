/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import JsonDeriving
import Test.Runner

open Json

namespace Test.Enum

@[json_enum SCREAMING_SNAKE_CASE (unplaced := "NONE")]
inductive Status where
  | met
  | workOut
  | unplaced
deriving ToJson, FromJson, BEq, Repr

@[json_enum kebab-case]
inductive Move where
  | lineRoundTrip
  | swap
deriving ToJson, FromJson, BEq, Repr

@[json_enum camelCase]
inductive Camel where
  | read_name
  | WORK_OUT
deriving ToJson, FromJson, BEq, Repr

/-- Two vocabularies embedded in a third, under their own conventions rather than its. -/
@[json_enum snake_case (hTypes3d := "h_types_3d")]
inductive Step where
  | readName
  | move (m : Move)
  | hTypes3d
  | status (s : Status)
deriving ToJson, FromJson, BEq, Repr

/-- An embedding two deep, which is written as the innermost member is. -/
@[json_enum]
inductive Outer where
  | step (s : Step)
  | done
deriving ToJson, FromJson, BEq, Repr

/-- The attribute with no convention: the constructors as written. -/
@[json_enum]
inductive AsWritten where
  | readName
  | WORK_OUT
deriving ToJson, FromJson, BEq, Repr

/-- No attribute: derived as before enumerations existed, with no declarations added. -/
inductive Plain where
  | readName
  | WORK_OUT
deriving ToJson, FromJson, BEq, Repr

@[json_enum]
private inductive Hidden where
  | a
  | b
deriving ToJson, FromJson

@[json_enum]
inductive Nothing where
deriving ToJson, FromJson

example : ExactJson Step := inferInstance
example : ExactJson Outer := inferInstance
example : ExactJson Hidden := inferInstance
example : ExactJson Nothing := inferInstance

/--
The codec of `Step` is a bijection between steps and the JSON values the decoder accepts: each
value read back is the value written, and each value accepted is a value written.

The left conjunct is the round trip for every step; the right says that a `j` decoded as `x` is
`toJson x`. The two classes `LawfulJson` and `ExactJson` supply them.
-/
theorem step_bijection :
    (∀ x : Step, (fromJson? (toJson x) : Except String Step) = .ok x) ∧
      (∀ (j : Json) (x : Step), (fromJson? j : Except String Step) = .ok x → j = toJson x) :=
  ⟨LawfulJson.fromJson?_toJson, ExactJson.eq_toJson_of_fromJson?⟩

-- Without the attribute, nothing beyond the two codecs is declared.
#guard_msgs (drop info) in
#check_failure Plain.all
#guard_msgs (drop info) in
#check_failure Plain.toJsonString
/--
error: failed to synthesize
  LawfulJson Plain

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth LawfulJson Plain

example : LawfulJson Step := inferInstance
example : LawfulJson Outer := inferInstance
example : LawfulJson AsWritten := inferInstance
example : LawfulJson Hidden := inferInstance
example : LawfulJson Nothing := inferInstance
example : LawfulJson (Option Status) := inferInstance

/--
A step's string is the string its JSON holds, so text built from `toJsonString` (a CSV cell, a
prompt) reads back through the JSON decoder. It is the property a caller writing text relies on.

`toJson x = .str (toJsonString x)` says the encoding is the JSON string whose contents are
`toJsonString x`, for every `x`; `JsonEnum.toJson_eq_str` is the derived instance's field.
-/
theorem step_toJson (x : Step) : toJson x = .str (toJsonString x) := JsonEnum.toJson_eq_str x

/--
An embedded member is written as the inner member is, which is what lets one vocabulary stand in
several others under the strings it already has.

The left side is the string of the step that carries a move, the right the string of the move
itself; they are equal for every move, by evaluation of both for each.
-/
theorem step_move_string (m : Move) : toJsonString (Step.move m) = toJsonString m := by
  cases m <;> rfl

/--
No two values of `Outer` share a string, two levels of embedding included, which is what lets the
string stand for the value. The derivation refuses a type where two would; this checks the result.

`List.Nodup` holds of a list with no two equal entries; the list is the strings of every value,
and string equality is decided character by character.
-/
theorem outer_all_nodup : (JsonEnum.all : List Outer).map toJsonString |>.Nodup := by decide

/-- The derived list has no repeats, for the embedding too, as a theorem and not by `decide`. -/
theorem outer_nodup_all : (JsonEnum.all : List Outer).Nodup := JsonEnum.nodup_all

/-- error: cannot derive a JSON enumeration for Test.Enum.Clash: Test.Enum.Clash.oneTwo and Test.Enum.Clash.one_two would both be written as "one_two" -/
#guard_msgs in
@[json_enum snake_case]
inductive Clash where
  | oneTwo
  | one_two
deriving ToJson

/-- error: cannot derive a JSON enumeration for Test.Enum.EmbeddedClash: Test.Enum.EmbeddedClash.swap and Test.Enum.EmbeddedClash.move Test.Enum.Move.swap would both be written as "swap" -/
#guard_msgs in
@[json_enum]
inductive EmbeddedClash where
  | swap
  | move (m : Move)
deriving FromJson

/-- error: cannot derive a JSON enumeration for Test.Enum.Scope: the constructor Test.Enum.Scope.all has the name of a declaration the derivation adds, Test.Enum.Scope.all; rename the constructor -/
#guard_msgs in
@[json_enum]
inductive Scope where
  | all
  | none
deriving ToJson

/-- error: cannot derive a JSON enumeration for Test.Enum.Key: the constructor Test.Enum.Key.jsonKey has the name of a declaration the derivation adds, Test.Enum.Key.jsonKey; rename the constructor -/
#guard_msgs in
@[json_enum]
inductive Key where
  | jsonKey
deriving FromJson

/-- error: cannot derive a JSON enumeration for Test.Enum.Loop: Test.Enum.Loop.again takes Test.Enum.Loop itself as its argument, and an enumeration cannot contain itself -/
#guard_msgs in
@[json_enum]
inductive Loop where
  | again (l : Loop)
  | stop
deriving ToJson

/-- error: cannot derive a JSON enumeration for Test.Enum.Blank: the constructor Test.Enum.Blank._ would be written as the empty string; give it a string of its own -/
#guard_msgs in
@[json_enum camelCase]
inductive Blank where
  | _
deriving ToJson

/-- error: cannot derive a JSON enumeration for Test.Enum.Carries: the argument of Test.Enum.Carries.count is of type Nat, which has no derived JSON enumeration codec, so derive it first, under json_enum -/
#guard_msgs in
@[json_enum]
inductive Carries where
  | count (n : Nat)
deriving ToJson

/-- error: cannot derive a JSON enumeration for Test.Enum.Renamed: Test.Enum.Renamed.move is written as its argument is, and takes no string of its own -/
#guard_msgs in
@[json_enum (move := "m")]
inductive Renamed where
  | move (m : Move)
deriving ToJson

/-- error: Test.Enum.Missing has no constructor nope -/
#guard_msgs in
@[json_enum (nope := "x")]
inductive Missing where
  | here

/-- error: json_enum applies to inductive types other than structures; Test.Enum.Point is a structure, whose keys json_keys names -/
#guard_msgs in
@[json_enum]
structure Point where
  x : Nat

private def encodesTo [ToJson α] (name : String) (v : α) (expected : String) : TestCase where
  name := name
  run :=
    let got := compress (toJson v)
    if got == expected then pure () else throw (IO.userError s!"encoded as {got}")

/-- Every member of the type through the printer and the parser and back. -/
private def everyMemberRoundTrips (name : String) (α : Type) [ToJson α] [FromJson α] [BEq α]
    [Repr α] [JsonEnum α] : TestCase where
  name := name
  run := for v in (JsonEnum.all : List α) do
    match Json.parse (compress (toJson v)) with
    | .error e => throw (IO.userError s!"the text did not parse: {e}")
    | .ok j =>
      match fromJson? j with
      | .ok (w : α) => unless w == v do throw (IO.userError s!"came back as {repr w}")
      | .error e => throw (IO.userError s!"failed to decode: {e}")

private def refusedWith (name : String) (α : Type) [FromJson α] (j : Json) (message : String) :
    TestCase where
  name := name
  run :=
    match fromJson? (α := α) j with
    | .error e => unless e == message do throw (IO.userError s!"refused with {e}")
    | .ok _ => throw (IO.userError "accepted")

def all : Array TestCase := #[
  encodesTo "SCREAMING_SNAKE_CASE" Status.workOut "\"WORK_OUT\"",
  encodesTo "an override beats the convention" Status.unplaced "\"NONE\"",
  encodesTo "kebab-case" Move.lineRoundTrip "\"line-round-trip\"",
  encodesTo "camelCase from names in other conventions" Camel.WORK_OUT "\"workOut\"",
  encodesTo "snake_case" Step.readName "\"read_name\"",
  encodesTo "an embedded member keeps its own convention" (Step.status .workOut) "\"WORK_OUT\"",
  encodesTo "an embedding two deep" (Outer.step (.move .swap)) "\"swap\"",
  encodesTo "the attribute with no convention keeps the names" AsWritten.WORK_OUT "\"WORK_OUT\"",
  encodesTo "no attribute writes a constructor as its name" Plain.WORK_OUT "\"WORK_OUT\"",
  expect "no attribute still accepts a constructor as an object of one field"
    (match (fromJson? (.obj #[("WORK_OUT", .null)]) : Except String Plain) with
      | .ok v => v == .WORK_OUT
      | .error _ => false),
  expect "no attribute still accepts a constructor as a string"
    (match (fromJson? (.str "readName") : Except String Plain) with
      | .ok v => v == .readName
      | .error _ => false),
  expectEq "all lists the members in order, embedded ones in their own order"
    ((JsonEnum.all : List Step).map toJsonString)
    ["read_name", "line-round-trip", "swap", "h_types_3d", "MET", "WORK_OUT", "NONE"],
  everyMemberRoundTrips "every step" Step,
  everyMemberRoundTrips "every outer value" Outer,
  everyMemberRoundTrips "every camel" Camel,
  refusedWith "an unknown string names the type and the string" Step (.str "work_out")
    "no member of Test.Enum.Step is written \"work_out\"",
  refusedWith "a string longer than every member" Step (.str (String.ofList (List.replicate 100 'a')))
    s!"no member of Test.Enum.Step is written \"{String.ofList (List.replicate 100 'a')}\"",
  refusedWith "a member's Lean name is not accepted under a convention" Status (.str "workOut")
    "no member of Test.Enum.Status is written \"workOut\"",
  refusedWith "a value that is not a string" Step (.obj #[("read_name", .null)])
    "expected a string naming a member of Test.Enum.Step",
  refusedWith "a type with no members refuses everything" Nothing (.str "")
    "no member of Test.Enum.Nothing is written \"\""
]

end Test.Enum
