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
number holding integers exactly only to `2 ^ 53 - 1`; the narrower unsigned types and `Fin n` are
numbers, and a number out of their range is refused.

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

instance : ToJson UInt8 := ⟨fun v => toJson v.toNat⟩
instance : FromJson UInt8 := ⟨fun j => do
  let n ← getNat? j
  if h : n < UInt8.size then .ok (UInt8.ofNatLT n h) else .error "value is too large for UInt8"⟩

instance : ToJson UInt16 := ⟨fun v => toJson v.toNat⟩
instance : FromJson UInt16 := ⟨fun j => do
  let n ← getNat? j
  if h : n < UInt16.size then .ok (UInt16.ofNatLT n h) else .error "value is too large for UInt16"⟩

instance : ToJson UInt32 := ⟨fun v => toJson v.toNat⟩
instance : FromJson UInt32 := ⟨fun j => do
  let n ← getNat? j
  if h : n < UInt32.size then .ok (UInt32.ofNatLT n h) else .error "value is too large for UInt32"⟩

/--
A number below `n`. The padding a number may ask for is bounded by the digits of `n` rather than by
the general thousand, which refuses a long text sooner and lets every value of `Fin n` read back,
however large `n` is.
-/
def finFromJson? (n : Nat) : Json → Except String (Fin n)
  | num x =>
    match x.toNat? (toString n).length with
    | some v => if h : v < n then .ok ⟨v, h⟩ else .error s!"expected a natural number below {n}"
    | none => .error s!"expected a natural number below {n}"
  | _ => .error "expected a number"

instance : ToJson (Fin n) := ⟨fun i => toJson i.val⟩
instance : FromJson (Fin n) := ⟨finFromJson? n⟩

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

/--
A natural number below `2 ^ 64` round trips with no further hypothesis. Every unsigned type's
values are below that bound, so this is the padding condition of `nat_roundTrip` discharged once
for all of them.

`h : n < 2 ^ 64` bounds `n` to twenty digits, and `Number.exponent_ofNat_le` turns that into an
exponent of at most twenty, well inside the thousand `nat_roundTrip` asks for. The conclusion is
`.ok n`.
-/
theorem nat_roundTrip_of_lt {n : Nat} (h : n < 2 ^ 64) :
    (fromJson? (toJson n) : Except String Nat) = .ok n :=
  nat_roundTrip (by
    have := Number.exponent_ofNat_le (k := 20) (Nat.lt_of_lt_of_le h (by decide)); omega)

/--
Folding the decimal reader over digits computes their value. It is the inductive step of
`decodeNat?_toString`, stated for any step function that does on a digit what the reader does.

`hf` says `f` appends a digit to an accumulated value, `h` that every character of `l` is a digit,
and the conclusion is the fold's result: `ofDigitChars`, core's value of a digit string, starting
from `a`. With a character that is not a digit the claim would not hold, which is why `h` is asked.
-/
private theorem foldl_digits (f : Option Nat → Char → Option Nat)
    (hf : ∀ v c, c.isDigit → f (some v) c = some (v * 10 + (c.toNat - '0'.toNat)))
    (l : List Char) (a : Nat) (h : ∀ c ∈ l, c.isDigit) :
    l.foldl f (some a) = some (Nat.ofDigitChars 10 l a) := by
  induction l generalizing a with
  | nil => simp
  | cons c cs ih =>
    rw [List.foldl_cons, hf a c (h c (by simp)), ih _ (fun c' hc' => h c' (by simp [hc'])),
      Nat.ofDigitChars_cons, Nat.mul_comm]

/--
The decimal reader gives back any natural number written in decimal, when the numeral is within its
digit limit. It is what makes the decimal-string encoding of `UInt64` and `USize` round trip.

`hlen` says the numeral, `Nat.toDigits 10 n`, has at most `k` digits, `k` being the limit the
reader enforces. The conclusion is `some n`: the reader neither refuses the numeral nor reads a
different number from it.
-/
theorem decodeNat?_toString {n k : Nat} (hlen : (Nat.toDigits 10 n).length ≤ k) :
    decodeNat? (toString n) k = some n := by
  have hne := Nat.toDigits_ne_nil (n := n) (b := 10)
  unfold decodeNat?
  simp only [Nat.toString_eq_ofList_toDigits, String.length_ofList,
    String.foldl_eq_foldl_toList, String.toList_ofList]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [hne]; omega))]
  rw [foldl_digits _ ?_ _ 0 (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)]
  · simp
  · intro v c hc
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hc
    have : ('0' ≤ c && c ≤ '9') = true := by
      simpa using (⟨hc.1, hc.2⟩ : '0' ≤ c ∧ c ≤ '9')
    simp [this]

/--
A natural number below `2 ^ 64` written as a decimal string reads back. `UInt64` and `USize` are
encoded that way, so this is their round trip apart from the range check.

`h : n < 2 ^ 64` puts the numeral at twenty digits at most, inside the reader's default limit of a
thousand, and the conclusion is `.ok n`.
-/
theorem bignum_roundTrip {n : Nat} (h : n < 2 ^ 64) : bignumFromJson? (bignumToJson n) = .ok n := by
  have hlen : (Nat.toDigits 10 n).length ≤ 1000 := Nat.le_trans
    ((Nat.length_toDigits_le_iff (k := 20) (by decide) (by decide)).2
      (Nat.lt_of_lt_of_le h (by decide)))
    (by decide)
  show (match decodeNat? (toString n) 1000 with
    | some v => Except.ok v | none => Except.error _) = _
  rw [decodeNat?_toString hlen]

/--
A value of `Fin n` encoded and decoded again is the value it was, for every `n`. The decoder bounds
padding by the digits of `n`, and no value below `n` has more trailing zeros than `n` has digits.

`i : Fin n` is any value; there is no hypothesis. The conclusion is `.ok i`, the bound check having
passed because `i` is below `n` and the padding check because of `Number.exponent_ofNat_le`.
-/
theorem fin_roundTrip {n : Nat} (i : Fin n) :
    (fromJson? (toJson i) : Except String (Fin n)) = .ok i := by
  have hlen : i.val < 10 ^ (toString n).length := by
    have := (Nat.length_toDigits_le_iff (b := 10) (n := n) (k := (Nat.toDigits 10 n).length)
      (by decide) Nat.length_toDigits_pos).1 (Nat.le_refl _)
    rw [Nat.toString_eq_ofList_toDigits, String.length_ofList]
    exact Nat.lt_trans i.isLt this
  show finFromJson? n (num (Number.ofNat i.val)) = _
  simp only [finFromJson?]
  rw [Number.toNat?_ofNat (Number.exponent_ofNat_le hlen)]
  simp [i.isLt]

/-! ## Lawful codecs

`LawfulJson α` says that `α`'s codec round trips for every value, so a proof about a type built
from others can ask for it of its parts. `Nat` and `Int` have no instance, their round trip failing
for a number with more than a thousand trailing zeros (`nat_roundTrip`); nor do `Float`, whose NaN
does not come back as the same bits, `String.Slice`, which comes back as a slice of a new string,
and `Std.TreeMap`, which is rebuilt by insertion and so not necessarily into the same tree. The
unsigned types and `Fin n` have one, a bounded type being how an integer field is made lawful.
`Option α` has one when `α`'s encoding is never `null`, which `NonNullJson` records.
-/

/-- Decoding the encoding of any value gives back that value. -/
class LawfulJson (α : Type u) [ToJson α] [FromJson α] : Prop where
  fromJson?_toJson : ∀ x : α, (fromJson? (toJson x) : Except String α) = .ok x

/--
Two values with the same encoding are the same value. It is what a lawful codec buys a caller
beyond reading back: the encoding can stand in for the value as a key, a cache entry or a test
expectation without two values being confused.

`toJson a = toJson b` says the encodings are equal as `Json` trees, not merely as text, and the
conclusion `a = b` is equality in `α`. Decoding both sides of the hypothesis gives `.ok a` and
`.ok b` by `fromJson?_toJson`, and `Except.ok` is injective.
-/
theorem LawfulJson.toJson_injective [ToJson α] [FromJson α] [LawfulJson α] {a b : α}
    (h : toJson a = toJson b) : a = b := by
  have := LawfulJson.fromJson?_toJson (α := α) a
  rw [h, LawfulJson.fromJson?_toJson] at this
  exact Except.ok.inj this |>.symm

/-- No value is encoded as `null`, which is what lets `Option α` round trip. -/
class NonNullJson (α : Type u) [ToJson α] : Prop where
  toJson_ne_null : ∀ x : α, toJson x ≠ null

instance : LawfulJson Json := ⟨json_roundTrip⟩
instance : LawfulJson Number := ⟨number_roundTrip⟩
instance : LawfulJson Bool := ⟨bool_roundTrip⟩
instance : LawfulJson String := ⟨string_roundTrip⟩
instance : LawfulJson Unit := ⟨fun () => unit_roundTrip⟩
instance : LawfulJson Empty := ⟨nofun⟩
instance : LawfulJson System.FilePath := ⟨fun _ => rfl⟩
instance : LawfulJson Structured := ⟨fun | .arr _ => rfl | .obj _ => rfl⟩
instance : LawfulJson (Fin n) := ⟨fin_roundTrip⟩

-- A bounded unsigned value is its `Nat` encoded, then range checked, which it passes.
instance : LawfulJson UInt8 := ⟨fun v => by
  show (do let n ← (fromJson? (toJson v.toNat) : Except String Nat); _) = _
  rw [nat_roundTrip_of_lt (Nat.lt_of_lt_of_le v.toNat_lt_size (by decide))]
  exact dite_eq_left v.toNat_lt_size⟩

instance : LawfulJson UInt16 := ⟨fun v => by
  show (do let n ← (fromJson? (toJson v.toNat) : Except String Nat); _) = _
  rw [nat_roundTrip_of_lt (Nat.lt_of_lt_of_le v.toNat_lt_size (by decide))]
  exact dite_eq_left v.toNat_lt_size⟩

instance : LawfulJson UInt32 := ⟨fun v => by
  show (do let n ← (fromJson? (toJson v.toNat) : Except String Nat); _) = _
  rw [nat_roundTrip_of_lt (Nat.lt_of_lt_of_le v.toNat_lt_size (by decide))]
  exact dite_eq_left v.toNat_lt_size⟩

instance : LawfulJson UInt64 := ⟨fun v => by
  show (do let n ← bignumFromJson? (bignumToJson v.toNat); _) = _
  rw [bignum_roundTrip v.toNat_lt_size]
  exact dite_eq_left v.toNat_lt_size⟩

instance : LawfulJson USize := ⟨fun v => by
  show (do let n ← bignumFromJson? (bignumToJson v.toNat); _) = _
  rw [bignum_roundTrip (Nat.lt_of_lt_of_le v.toNat_lt_size USize.size_le)]
  exact dite_eq_left v.toNat_lt_size⟩

instance {α : Type} [ToJson α] [FromJson α] [LawfulJson α] : LawfulJson (Array α) :=
  ⟨array_roundTrip LawfulJson.fromJson?_toJson⟩

instance {α : Type} [ToJson α] [FromJson α] [LawfulJson α] : LawfulJson (List α) :=
  ⟨list_roundTrip LawfulJson.fromJson?_toJson⟩

instance {α β : Type} [ToJson α] [FromJson α] [LawfulJson α] [ToJson β] [FromJson β]
    [LawfulJson β] : LawfulJson (α × β) :=
  ⟨prod_roundTrip LawfulJson.fromJson?_toJson LawfulJson.fromJson?_toJson⟩

instance {α : Type} [ToJson α] [FromJson α] [LawfulJson α] [NonNullJson α] :
    LawfulJson (Option α) :=
  ⟨fun
    | none => option_none_roundTrip
    | some a =>
      option_some_roundTrip LawfulJson.fromJson?_toJson a (NonNullJson.toJson_ne_null a)⟩

instance : NonNullJson Number := ⟨fun _ => nofun⟩
instance : NonNullJson Bool := ⟨fun _ => nofun⟩
instance : NonNullJson String := ⟨fun _ => nofun⟩
instance : NonNullJson Unit := ⟨fun _ => nofun⟩
instance : NonNullJson Empty := ⟨nofun⟩
instance : NonNullJson System.FilePath := ⟨fun _ => nofun⟩
instance : NonNullJson Structured := ⟨fun | .arr _ => nofun | .obj _ => nofun⟩
instance : NonNullJson (Fin n) := ⟨fun _ => nofun⟩
instance : NonNullJson UInt8 := ⟨fun _ => nofun⟩
instance : NonNullJson UInt16 := ⟨fun _ => nofun⟩
instance : NonNullJson UInt32 := ⟨fun _ => nofun⟩
instance : NonNullJson UInt64 := ⟨fun _ => nofun⟩
instance : NonNullJson USize := ⟨fun _ => nofun⟩
instance [ToJson α] : NonNullJson (Array α) := ⟨fun _ => nofun⟩
instance [ToJson α] : NonNullJson (List α) := ⟨fun _ => nofun⟩
instance [ToJson α] [ToJson β] : NonNullJson (α × β) := ⟨fun _ => nofun⟩

/-! ## What a derived codec's proofs need

A derived encoder builds an object as `mkObj (List.flatten parts)`, one part per field: a single
pair, or `opt k v` for an optional field. Its decoder looks each key up with `getObjValD`. These
say what that lookup finds, given that no other part carries the key, which the handler checks
before it generates anything and the generated proof shows one pair of keys at a time.
-/

/--
A field's part does not carry another field's key. A derived codec's proof needs this of every
pair of fields, so it is stated for one part and one other key at a time, leaving only the
inequality of two string literals to check.

`k ∉ [(k', v)].map Prod.fst` says the part, the single pair under `k'`, has no pair under `k`.
`h : k ≠ k'` is all it needs, the value playing no part.
-/
theorem not_mem_keys_single {k k' : String} {v : Json} (h : k ≠ k') :
    k ∉ [(k', v)].map Prod.fst := by
  simpa using h

/--
An optional field's part does not carry another field's key, whether or not the field is present.
It is the counterpart of `not_mem_keys_single` for a part that may be empty.

`k ∉ (opt k' o).map Prod.fst` says the part has no pair under `k`. When `o` is `none` the part is
empty, and when it is `some v` it is the single pair under `k'`, so `h : k ≠ k'` covers both.
-/
theorem not_mem_keys_opt [ToJson α] {k k' : String} {o : Option α} (h : k ≠ k') :
    k ∉ (opt k' o).map Prod.fst := by
  cases o with
  | none => simp [opt]
  | some _ => simpa [opt] using h

/--
Looking up a field's key in an object built from parts finds the value its own part put there,
whatever comes before it, as long as nothing after it carries the same key. It is the step
`getObjValD_mkObj_get` takes once the parts are split around the field's.

`pre` and `post` are the parts before and after the field's, `[(k, v)]`. `hpost` says no part in
`post` has a pair under `k`; nothing is asked of `pre`, lookup taking the last field of a name. The
conclusion is that `getObjValD` answers `v` itself, not the `null` it gives for a missing key.
-/
private theorem getObjValD_mkObj_field {pre post : List (List (String × Json))} {k : String}
    {v : Json} (hpost : ∀ p ∈ post, k ∉ p.map Prod.fst) :
    (mkObj (List.flatten (pre ++ [(k, v)] :: post))).getObjValD k = v := by
  have hnone : findLast? (List.flatten post).toArray k = none := by
    rw [findLast?_eq_none_iff]
    simpa [fieldNames, List.mem_flatten] using hpost
  simp only [mkObj, getObjValD, getObjVal?, List.flatten_append, List.flatten_cons,
    ← List.append_assoc, ← List.append_toArray, findLast?_append, hnone, Option.none_or]
  simp [findLast?]
  rfl

/--
A list with an element at `i` is what comes before it, the element, and what comes after. It is
what lets a lookup be stated by position, the parts before and after being read off the list
rather than written out again.

`h : l[i]? = some p` says `p` is at `i`, which also puts `i` in bounds. The conclusion splits `l`
into `l.take i`, `p` and `l.drop (i + 1)`, so nothing is lost or repeated at the seams.
-/
private theorem eq_take_cons_drop {l : List α} {i : Nat} {p : α} (h : l[i]? = some p) :
    l = l.take i ++ p :: l.drop (i + 1) := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 h
  rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]

/--
Looking up a field's key in an object built from parts finds the value its own part put there, as
long as no later part carries the same key. It is how a proof that a derived decoder reads back its
encoder's output finds each field, the parts being those of the encoder and `i` the field's place.

`hi : parts[i]? = some [(k, v)]` says the field's part is the single pair under `k`. `hpost` says no
part after it has a pair under `k`; nothing is asked of the parts before, lookup taking the last
field of a name. The conclusion is that `getObjValD` answers `v` itself, not the `null` it gives
for a missing key.
-/
theorem getObjValD_mkObj_get {parts : List (List (String × Json))} {i : Nat} {k : String}
    {v : Json} (hi : parts[i]? = some [(k, v)])
    (hpost : ∀ p ∈ parts.drop (i + 1), k ∉ p.map Prod.fst) :
    (mkObj parts.flatten).getObjValD k = v := by
  rw [eq_take_cons_drop hi]
  exact getObjValD_mkObj_field hpost

/--
Looking up an optional field's key in an object built from parts finds the encoding of the field,
`null` when it is absent and the value's encoding when present, as long as no other part carries
the key. It is what lets a derived decoder read an optional field back through `Option`'s decoder
whether or not the encoder wrote it.

`hi : parts[i]? = some (opt k o)` says the field's part is the optional one under `k`. `hpre` and
`hpost` say no part before or after it has a pair under `k`; both are needed, since an absent field
leaves lookup to fall through to the others. The conclusion is `toJson o`, which is `null` for
`none` and `toJson v` for `some v`, the two answers the lookup gives.
-/
theorem getObjValD_mkObj_get_opt [ToJson α] {parts : List (List (String × Json))} {i : Nat}
    {k : String} {o : Option α} (hi : parts[i]? = some (opt k o))
    (hpre : ∀ p ∈ parts.take i, k ∉ p.map Prod.fst)
    (hpost : ∀ p ∈ parts.drop (i + 1), k ∉ p.map Prod.fst) :
    (mkObj parts.flatten).getObjValD k = toJson o := by
  rw [eq_take_cons_drop hi]
  generalize parts.take i = pre at hpre ⊢
  generalize parts.drop (i + 1) = post at hpost ⊢
  cases o with
  | some v => exact getObjValD_mkObj_field hpost
  | none =>
    have hnone : findLast? (List.flatten (pre ++ post)).toArray k = none := by
      rw [findLast?_eq_none_iff]
      simp only [fieldNames, List.map_flatten, List.mem_flatten, List.map_append, List.mem_append,
        List.mem_map, not_exists, not_and]
      grind
    simp [mkObj, getObjValD, getObjVal?, opt, List.flatten_append] at hnone ⊢
    simp [hnone]
    rfl

end

end Json
