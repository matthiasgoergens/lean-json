/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Basic
public import Std.Data.TreeMap

public section

namespace Json

@[expose] section

universe u v

/-!
Encoding to and decoding from `Json`.

A decoder returns `Except String α`, and the message is written for a person to read. `none` is
`null` and `some a` is whatever `a` is, so `Option (Option α)` does not round trip, as in every
library that makes that choice. `USize` and `UInt64` are written as decimal strings, a JavaScript
number holding integers exactly only to `2 ^ 53 - 1`.

The handlers for `deriving ToJson, FromJson` are in the companion package, which is where the
frontend may be imported. What they generate calls the helpers at the end of this file.
-/

/-- Types that can be encoded as JSON. -/
class ToJson (α : Type u) where
  toJson : α → Json

/-- Types that can be decoded from JSON. -/
class FromJson (α : Type u) where
  fromJson? : Json → Except String α

export ToJson (toJson)
export FromJson (fromJson?)

/-! ## Values that carry structure -/

/-- The two shapes a codec can descend into. -/
inductive Structured where
  | arr (elems : Array Json)
  | obj (fields : Array (String × Json))
deriving Inhabited, Repr, BEq

def Structured.toJson : Structured → Json
  | .arr elems => .arr elems
  | .obj fields => .obj fields

def Structured.fromJson? : Json → Except String Structured
  | .arr elems => .ok (.arr elems)
  | .obj fields => .ok (.obj fields)
  | _ => .error "expected an array or an object"

instance : ToJson Structured := ⟨Structured.toJson⟩
instance : FromJson Structured := ⟨Structured.fromJson?⟩

/-! ## Instances -/

instance : ToJson Json := ⟨id⟩
instance : FromJson Json := ⟨Except.ok⟩

instance : ToJson Number := ⟨num⟩
instance : FromJson Number := ⟨getNum?⟩

instance : ToJson Bool := ⟨bool⟩
instance : FromJson Bool := ⟨getBool?⟩

instance : ToJson String := ⟨str⟩
instance : FromJson String := ⟨getStr?⟩

instance : ToJson Nat := ⟨fun n => num (Number.ofNat n)⟩
instance : FromJson Nat := ⟨getNat?⟩

instance : ToJson Int := ⟨fun i => num (Number.ofInt i)⟩
instance : FromJson Int := ⟨getInt?⟩

instance : ToJson Unit := ⟨fun _ => obj #[]⟩
instance : FromJson Unit := ⟨fun j =>
  match j with
  | obj #[] => .ok ()
  | _ => .error "expected an empty object"⟩

instance : ToJson Empty := ⟨nofun⟩
instance : FromJson Empty := ⟨fun _ => .error "Empty has no values to decode into"⟩

instance : ToJson String.Slice := ⟨fun s => str s.copy⟩
instance : FromJson String.Slice := ⟨fun j => String.toSlice <$> getStr? j⟩

instance : ToJson System.FilePath := ⟨fun p => str p.toString⟩
instance : FromJson System.FilePath := ⟨fun j => System.FilePath.mk <$> getStr? j⟩

def arrayToJson [ToJson α] (a : Array α) : Json := arr (a.map toJson)

def arrayFromJson? [FromJson α] : Json → Except String (Array α)
  | arr elems => elems.mapM fromJson?
  | _ => .error "expected an array"

instance [ToJson α] : ToJson (Array α) := ⟨arrayToJson⟩
instance [FromJson α] : FromJson (Array α) := ⟨arrayFromJson?⟩

instance [ToJson α] : ToJson (List α) := ⟨fun l => arrayToJson l.toArray⟩
instance [FromJson α] : FromJson (List α) := ⟨fun j => Array.toList <$> arrayFromJson? j⟩

/--
`none` is `null`, and `some a` is whatever `a` is. As in every library that makes this choice,
`Option (Option α)` therefore does not round trip, `none` and `some none` sharing an encoding.
-/
def optionToJson [ToJson α] : Option α → Json
  | none => null
  | some a => toJson a

def optionFromJson? [FromJson α] : Json → Except String (Option α)
  | null => .ok none
  | j => some <$> fromJson? j

instance [ToJson α] : ToJson (Option α) := ⟨optionToJson⟩
instance [FromJson α] : FromJson (Option α) := ⟨optionFromJson?⟩

instance [ToJson α] [ToJson β] : ToJson (α × β) :=
  ⟨fun (a, b) => arr #[toJson a, toJson b]⟩

-- Matching a list rather than an array literal, so that the equation lemmas a proof needs are
-- generated: `#[ja, jb]` as a pattern defeats them.
def prodFromJson? {α : Type u} {β : Type v} [FromJson α] [FromJson β] :
    Json → Except String (α × β)
  | arr elems =>
    match elems.toList with
    | [ja, jb] => do
      let ⟨a⟩ : ULift.{v} α := ← (fromJson? ja).map ULift.up
      let ⟨b⟩ : ULift.{u} β := ← (fromJson? jb).map ULift.up
      return (a, b)
    | _ => .error "expected an array of two elements"
  | _ => .error "expected an array of two elements"

instance {α : Type u} {β : Type v} [FromJson α] [FromJson β] : FromJson (α × β) :=
  ⟨prodFromJson?⟩

/--
A natural number written as a decimal string rather than as a JSON number.

`USize` and `UInt64` are encoded this way, following the same reasoning as every other library
that talks to JavaScript: JSON numbers have no range limit, but a JavaScript `Number` holds
integers exactly only up to `2 ^ 53 - 1`, so a value near the top of a 64-bit range would not
survive the trip.
-/
def bignumToJson (n : Nat) : Json := str (toString n)

/-- A decimal numeral of at most `maxDigits` digits, refusing anything longer unread. -/
def decodeNat? (s : String) (maxDigits : Nat := 1000) : Option Nat :=
  if s.isEmpty || maxDigits < s.length then
    none
  else
    s.foldl (init := some 0) fun acc c =>
      match acc with
      | none => none
      | some v => if '0' ≤ c && c ≤ '9' then some (v * 10 + (c.toNat - '0'.toNat)) else none

def bignumFromJson? (j : Json) (maxDigits : Nat := 1000) : Except String Nat := do
  let s ← getStr? j
  match decodeNat? s maxDigits with
  | some v => .ok v
  | none => .error "expected a string holding a decimal numeral"

instance : ToJson USize := ⟨fun v => bignumToJson v.toNat⟩
instance : FromJson USize := ⟨fun j => do
  let n ← bignumFromJson? j
  if h : n < USize.size then .ok (USize.ofNatLT n h) else .error "value is too large for USize"⟩

instance : ToJson UInt64 := ⟨fun v => bignumToJson v.toNat⟩
instance : FromJson UInt64 := ⟨fun j => do
  let n ← bignumFromJson? j
  if h : n < UInt64.size then .ok (UInt64.ofNatLT n h) else .error "value is too large for UInt64"⟩

/--
A finite `Float` is a number, exactly; the three values IEEE 754 has and JSON does not are the
strings `"NaN"`, `"Infinity"` and `"-Infinity"`, which is the encoding the other implementations
use.
-/
def floatToJson (x : Float) : Json :=
  match Number.ofFloat? x with
  | some n => num n
  | none => str (if x.isNaN then "NaN" else if x < 0.0 then "-Infinity" else "Infinity")

def floatFromJson? : Json → Except String Float
  | num n => .ok n.toFloat
  | str "NaN" => .ok (0.0 / 0.0)
  | str "Infinity" => .ok (1.0 / 0.0)
  | str "-Infinity" => .ok (-1.0 / 0.0)
  | _ => .error "expected a number, or \"NaN\", \"Infinity\" or \"-Infinity\""

instance : ToJson Float := ⟨floatToJson⟩
instance : FromJson Float := ⟨floatFromJson?⟩

instance {cmp} [ToJson α] : ToJson (Std.TreeMap String α cmp) :=
  ⟨fun m => obj (m.foldl (init := #[]) fun acc k v => acc.push (k, toJson v))⟩

instance {cmp} [FromJson α] : FromJson (Std.TreeMap String α cmp) := ⟨fun j => do
  let fields ← getObj? j
  fields.foldlM (init := ∅) fun m (k, v) => return m.insert k (← fromJson? v)⟩

/-! ## Helpers -/

def toStructured? [ToJson α] (v : α) : Except String Structured := fromJson? (toJson v)

/-- The field named `k`, decoded. A missing field decodes `null`, which an `Option` accepts. -/
def getObjValAs? (j : Json) (α : Type u) [FromJson α] (k : String) : Except String α :=
  fromJson? (j.getObjValD k)

def setObjValAs? (j : Json) {α : Type u} [ToJson α] (k : String) (v : α) : Except String Json :=
  j.setObjVal? k (toJson v)

/-- A field to include only when it has a value, for building objects out of optional parts. -/
def opt [ToJson α] (k : String) : Option α → List (String × Json)
  | none => []
  | some v => [(k, toJson v)]

/-- The string value, or the single field name, if there is exactly one. -/
def getTag? : Json → Option String
  | str tag => some tag
  | obj fields => if fields.size == 1 then fields[0]?.map Prod.fst else none
  | _ => none

/--
The fields of an encoded constructor whose tag is already known, which is what a derived
decoder needs once it has dispatched on the tag.
-/
def parseCtorFields (j : Json) (tag : String) (nFields : Nat)
    (fieldNames? : Option (Array String)) : Except String (Array Json) := do
  let payload ← j.getObjVal? tag
  match fieldNames? with
  | some names => names.mapM payload.getObjVal?
  | none =>
    if nFields == 1 then
      .ok #[payload]
    else
      let fields ← payload.getArr?
      if fields.size == nFields then .ok fields
      else .error s!"expected {nFields} fields, got {fields.size}"

/-- As `parseCtorFields`, but also handling a constructor with no arguments, encoded as its name. -/
def parseTagged (j : Json) (tag : String) (nFields : Nat)
    (fieldNames? : Option (Array String)) : Except String (Array Json) :=
  if nFields == 0 then do
    let s ← j.getStr?
    if s == tag then .ok #[] else .error s!"expected the tag {tag}, got {s}"
  else
    parseCtorFields j tag nFields fieldNames?


/-! ## What a derived codec needs

A derived decoder reaches its constructor's fields by position, and reaches a recursive position
through a function it is in the middle of defining, so neither can go through an instance. These
are what it calls instead.
-/

/-- The `i`th of a constructor's fields, without the panic that indexing carries. -/
def ctorField? (fields : Array Json) (i : Nat) : Except String Json :=
  match fields[i]? with
  | some j => .ok j
  | none => .error s!"expected more than {i} fields, got {fields.size}"

def arrayOf? (decode : Json → Except String α) : Json → Except String (Array α)
  | arr elems => elems.mapM decode
  | _ => .error "expected an array"

def listOf? (decode : Json → Except String α) (j : Json) : Except String (List α) :=
  Array.toList <$> arrayOf? decode j

def optionOf? (decode : Json → Except String α) : Json → Except String (Option α)
  | null => .ok none
  | j => some <$> decode j


/-! ## Round trips

What a decoder gives back is what the encoder was given. Each claim is stated for the pair of
instances it is about, and the ones with a hypothesis are those where the trip is conditional:
an integer whose canonical form needs more padding than the bound allows cannot be read back,
`some a` survives only when `a` does not itself encode as `null`, and a container survives
exactly when its elements do.
-/

/--
A `Json` value encoded and decoded again is the value it was. The instances for `Json` itself are
the identity pair, and recording that is what lets `Json` be used as a field type inside a derived
codec without any special case being made for it.

`toJson j` is `j` and `fromJson? j` is `.ok j`, so the equation holds by `rfl` for every value,
however deeply nested. There is no hypothesis, and none of the other round trips in this section
is appealed to, since no value of another type is involved.
-/
theorem json_roundTrip (j : Json) : (fromJson? (toJson j) : Except String Json) = .ok j := rfl

/--
A number encoded and decoded again is the number it was, with no normalisation on the way. A
caller can build a number the parser would never produce, one that is not canonical, and this says
such a value comes back as written rather than being quietly changed by the codec.

`toJson n` wraps `n` in the `num` constructor and `fromJson?` is `getNum?`, which unwraps it, so
the equation holds by `rfl`. Nothing inspects the mantissa or the exponent, which is why no
canonicity hypothesis appears.
-/
theorem number_roundTrip (n : Number) : (fromJson? (toJson n) : Except String Number) = .ok n :=
  rfl

/--
A boolean encoded and decoded again is the boolean it was. It is the simplest claim in this
section and one of the few that holds with no hypothesis at all, which is worth saying plainly
because most of the others are conditional.

`toJson b` wraps `b` in the `bool` constructor and `fromJson?` is `getBool?`, which unwraps it, so
the equation holds by `rfl` for both values of `Bool`.
-/
theorem bool_roundTrip (b : Bool) : (fromJson? (toJson b) : Except String Bool) = .ok b := rfl

/--
A string encoded and decoded again is the string it was. Escaping belongs to the printer and not
to the codec, so nothing here inspects the characters, and no code point can be lost or altered
between encoding and decoding.

`toJson s` wraps `s` in the `str` constructor and `fromJson?` is `getStr?`, which unwraps it, so
the equation holds by `rfl` for every string, whatever characters it holds.
-/
theorem string_roundTrip (s : String) : (fromJson? (toJson s) : Except String String) = .ok s :=
  rfl

/--
The unit value encoded and decoded again is the unit value. It is encoded as the empty object, and
this says the decoder accepts exactly that, which is what makes a derived codec for a constructor
with no fields read back.

`toJson ()` is `obj #[]`, and the decoder matches that pattern alone: an object with any field at
all is an error rather than a unit. The equation holds by `rfl`, and there is nothing to quantify
over, `Unit` having one value.
-/
theorem unit_roundTrip : (fromJson? (toJson ()) : Except String Unit) = .ok () := rfl

/--
An integer encoded and decoded again is the integer it was, whenever writing it out stays within
the padding bound. That bound exists because a short text can otherwise ask for an integer of a
billion digits, and this says the price is paid only by integers that are themselves enormous.

`h : (Number.ofInt i).exponent ≤ 1000` is the padding condition, and it is not vacuous:
`Number.le_exponent_normalizeAux` puts that exponent at the number of `i`'s trailing zeros, so the
only integers it excludes are those ending in more than a thousand of them. The conclusion says
decoding the encoding yields `.ok i`, the integer itself rather than something numerically equal
to it.
-/
theorem int_roundTrip {i : Int} (h : (Number.ofInt i).exponent ≤ 1000) :
    (fromJson? (toJson i) : Except String Int) = .ok i := by
  simp [toJson, fromJson?, getInt?, Number.toInt?_ofInt h]

/--
A natural number encoded and decoded again is the natural number it was, under the same padding
condition as an integer. The decoder adds a sign check to the integer one, and this says that
check never rejects a value that was non-negative to begin with.

`h : (Number.ofNat n).exponent ≤ 1000` again bounds the trailing zeros of the encoded number, so
it excludes only naturals ending in more than a thousand of them. The conclusion is `.ok n`. It
rests on `Number.toNat?_ofNat`, whose one step beyond the integer case is that `n` is non-negative
and so survives the extra check.
-/
theorem nat_roundTrip {n : Nat} (h : (Number.ofNat n).exponent ≤ 1000) :
    (fromJson? (toJson n) : Except String Nat) = .ok n := by
  simp [toJson, fromJson?, getNat?, Number.toNat?_ofNat h]

/--
`none` encoded and decoded again is `none`. It holds for any element type whatever, including one
whose own values do not round trip, since no value of that type takes part.

`toJson (none : Option α)` is `Json.null`, and `optionFromJson?` answers `.ok none` on exactly
that constructor, so the equation holds by `rfl`. The instances for `α` have to exist for the
statement to typecheck but are never called.
-/
theorem option_none_roundTrip {α : Type} [ToJson α] [FromJson α] :
    (fromJson? (toJson (none : Option α)) : Except String (Option α)) = .ok none := rfl

/--
`some a` encoded and decoded again is `some a`, when `a` itself round trips and is not encoded as
`null`. Encoding `none` as `null` is what makes the second condition necessary, and
`Option (Option α)` is the case that pays for it: `none` and `some none` share an encoding, so
one of the two has to lose.

`h` says `α` round trips, and is needed because the decoder calls `α`'s own decoder on the
payload. `hne : toJson a ≠ Json.null` is what keeps the decoder out of its `none` branch;
without it the claim would be false rather than merely unproved. The conclusion is `.ok (some a)`,
the constructor as well as the payload coming back.
-/
theorem option_some_roundTrip {α : Type} [ToJson α] [FromJson α]
    (h : ∀ a : α, (fromJson? (toJson a) : Except String α) = .ok a) (a : α)
    (hne : toJson a ≠ Json.null) :
    (fromJson? (toJson (some a)) : Except String (Option α)) = .ok (some a) := by
  show optionFromJson? (toJson a) = _
  unfold optionFromJson?
  split
  · next hnull => exact absurd hnull hne
  · simp [h a]
    rfl

/--
A pair encoded and decoded again is the pair it was, when both components round trip. A pair is
written as a two-element array, so this also says the decoder's shape check accepts what the
encoder writes, which a disagreement about arity would break.

`ha` and `hb` say each component type round trips, and both are used, the decoder calling each in
turn. The two types may live in different universes, which is why the decoder lifts each result
through `ULift` before pairing them; the conclusion is `.ok p` for the pair itself, so neither the
order of the components nor either of them is disturbed.
-/
theorem prod_roundTrip {α β : Type} [ToJson α] [FromJson α] [ToJson β] [FromJson β]
    (ha : ∀ a : α, (fromJson? (toJson a) : Except String α) = .ok a)
    (hb : ∀ b : β, (fromJson? (toJson b) : Except String β) = .ok b) (p : α × β) :
    (fromJson? (toJson p) : Except String (α × β)) = .ok p := by
  obtain ⟨a, b⟩ := p
  show prodFromJson? (arr #[toJson a, toJson b]) = _
  simp [prodFromJson?, ha a, hb b, Except.map]
  rfl

/--
An array encoded and decoded again is the array it was, when its elements round trip. Encoding
maps over the elements and decoding maps back, so what has to be shown is that a `mapM` of a
function that always succeeds and returns its input leaves the array alone.

`h` says `α` round trips, and is applied at each element. The conclusion is `.ok a` for the array
itself, so its length and the order of its elements are part of what is claimed. The empty array
is covered, and is the case in which `h` is never used.
-/
theorem array_roundTrip {α : Type} [ToJson α] [FromJson α]
    (h : ∀ a : α, (fromJson? (toJson a) : Except String α) = .ok a) (a : Array α) :
    (fromJson? (toJson a) : Except String (Array α)) = .ok a := by
  show arrayFromJson? (arrayToJson a) = _
  simp only [arrayToJson, arrayFromJson?, Array.mapM_map, Function.comp_def, h]
  show Array.mapM (fun x => pure x) a = pure a
  simpa using Array.mapM_pure (m := Except String) (f := id) (xs := a)

/--
A list encoded and decoded again is the list it was, when its elements round trip. Lists are
encoded through arrays, so nothing new is proved here, but this is the form a caller with a `List`
field actually needs.

`h` says `α` round trips, and the conclusion is `.ok l`. The encoder converts to an array and the
decoder converts back, so the claim is `array_roundTrip` at `l.toArray`, with `Array.toList`
undoing the conversion.
-/
theorem list_roundTrip {α : Type} [ToJson α] [FromJson α]
    (h : ∀ a : α, (fromJson? (toJson a) : Except String α) = .ok a) (l : List α) :
    (fromJson? (toJson l) : Except String (List α)) = .ok l := by
  show Array.toList <$> (fromJson? (toJson l.toArray) : Except String (Array α)) = _
  rw [array_roundTrip h l.toArray]
  rfl

end

end Json
