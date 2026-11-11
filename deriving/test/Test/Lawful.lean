/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import JsonDeriving
import Test.Codecs
import Test.Keys

open Json

namespace Test.Lawful

structure Tag where
  label : String
  on : Bool
deriving ToJson, FromJson

/-- Every shape a field can take here: renamed, nested, in a container, optional and absent. -/
@[json_keys snake_case (note? := "remark")]
structure Entry where
  mainTag : Tag
  otherTags : List Tag
  note? : Option String
  parent? : Option Tag
  pair : String × Array Bool
  raw : Json
deriving FromJson, ToJson

structure Box (α : Type) where
  val : α
  more? : Option α
deriving ToJson, FromJson

/-- Integers held in bounded types, which is what makes a structure with numbers lawful. -/
@[json_keys snake_case]
structure Reading where
  sensorId : UInt32
  channel : Fin 8
  seq : UInt64
  level? : Option UInt8
deriving ToJson, FromJson

structure Nothing where
deriving ToJson, FromJson

private structure Hidden where
  secret : String
deriving ToJson, FromJson

example : LawfulJson Tag := inferInstance
example : LawfulJson Entry := inferInstance
example : LawfulJson Nothing := inferInstance
example : LawfulJson Hidden := inferInstance
example : LawfulJson (Box Tag) := inferInstance
example : LawfulJson (Array (Option Entry)) := inferInstance
example : LawfulJson Reading := inferInstance

-- `Option (Option α)` does not round trip, and the instance for `Box` must not claim it does.
/--
error: failed to synthesize
  LawfulJson (Box (Option String))

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth LawfulJson (Box (Option String))

-- A field of a type without an instance leaves the codec derived and the instance out.
/--
error: failed to synthesize
  LawfulJson Codecs.Point

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#guard_msgs in
#synth LawfulJson Codecs.Point

/--
Two entries that encode alike are the same entry, so the encoding can serve as a key. It is the
consequence of the derived instance a caller is most likely to rely on.

`toJson a = toJson b` compares the two encodings as trees, and `a = b` is equality of entries,
every field of both, the absent optional ones included.
-/
theorem entry_toJson_injective {a b : Entry} (h : toJson a = toJson b) : a = b :=
  LawfulJson.toJson_injective h

/--
A structure whose fields hold `Nat`s round trips whenever its numbers do, which is all that can be
said, `Nat` itself round tripping only up to a thousand trailing zeros. The generated theorem takes
one hypothesis per field, and this discharges each from what is known of the field's type.

`h` says every natural number round trips, which is the assumption under which a `Snake` does;
the conclusion is that decoding the encoding of `s` gives `s`, under the renamed keys, and whether
or not its optional field is present.
-/
theorem snake_roundTrip (h : ∀ n : Nat, (fromJson? (toJson n) : Except String Nat) = .ok n)
    (s : Keys.Snake) : (fromJson? (toJson s) : Except String Keys.Snake) = .ok s := by
  apply Keys.Snake.fromJson?_toJson s (string_roundTrip _) (array_roundTrip h _) _
    (string_roundTrip _)
  cases s.gPerMol? with
  | none => exact option_none_roundTrip
  | some n => exact option_some_roundTrip h n nofun

/--
The derived decoder for `Person` reads back what its encoder wrote, with its nested `Point`, under
the assumption that the `Point`'s numbers do. It is the generated theorem used at a structure that
holds another derived structure.

`hx` and `hy` are about the one `Point` inside `p`, so nothing is assumed of any other number; the
conclusion is about `p` as a whole, its optional nickname included.
-/
theorem person_roundTrip (p : Codecs.Person)
    (hx : (fromJson? (toJson p.home.x) : Except String Nat) = .ok p.home.x)
    (hy : (fromJson? (toJson p.home.y) : Except String Nat) = .ok p.home.y) :
    (fromJson? (toJson p) : Except String Codecs.Person) = .ok p :=
  Codecs.Person.fromJson?_toJson p (string_roundTrip _)
    (array_roundTrip string_roundTrip _) (LawfulJson.fromJson?_toJson _)
    (Codecs.Point.fromJson?_toJson _ hx hy)

end Test.Lawful
