/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.FromTo
public import Json.Printer

public section

namespace Json

@[expose] section

universe u

/-!
Enumerations written as strings: a closed vocabulary such as `["MET", "WORK_OUT"]`, each member a
JSON string. A derived decoder dispatches on `stringKey?` of the text, a number that differs for
every pair of strings, through a balanced tree of comparisons. Each member's round trip is then one
evaluation of its key and a path down the tree, rather than a comparison with every string tried
before it, which makes the derived proof cost a little per member instead of growing with the
square of their number.
-/

/-- A type whose values are each written as a JSON string, and which has finitely many of them. -/
class JsonEnum (α : Type u) [ToJson α] where
  /-- Every value, each once. -/
  all : List α
  mem_all : ∀ x, x ∈ all
  nodup_all : all.Nodup
  /-- The string a value is written as, for text that is not JSON: a CSV cell, a prompt. -/
  toJsonString : α → String
  toJson_eq_str : ∀ x, toJson x = str (toJsonString x)

export JsonEnum (toJsonString)

/--
The bytes of `s` as the digits of a base 257 number, each byte plus one so that no digit is zero
and no two strings share a number, or `none` beyond `maxBytes`, which keeps an unknown text from
costing more than the longest member does.
-/
def stringKey? (maxBytes : Nat) (s : String) : Option Nat :=
  if s.utf8ByteSize ≤ maxBytes then
    -- Through the list of bytes, which the kernel evaluates in half the time a fold over the
    -- array takes, and this is evaluated once per member in a derived proof.
    some (s.toByteArray.data.toList.foldl (fun acc b => acc * 257 + b.toNat + 1) 0)
  else
    none

/-- The member of `typeName` written `s`, found by its key with `byKey`. -/
def decodeByKey (typeName : String) (maxBytes : Nat) (byKey : Nat → Option α) (s : String) :
    Except String α :=
  match (stringKey? maxBytes s).bind byKey with
  | some x => .ok x
  | none => .error s!"no member of {typeName} is written {compress (str s)}"

/-- The decoder of an enumeration, which accepts a string and nothing else. -/
def enumFromJson? (typeName : String) (ofString : String → Except String α) :
    Json → Except String α
  | str s => ofString s
  | _ => .error s!"expected a string naming a member of {typeName}"

/--
A string whose key is found by the lookup decodes as what the lookup found. A derived round trip
uses it once per member, with the key evaluated and the lookup followed down its tree.

`stringKey? maxBytes s = some k` says `s` is within the bound and has key `k`; `byKey k = some x`
says the lookup takes that key to `x`. Together they fix the `match` in `decodeByKey` on its
`some x` arm, which is `.ok x`.
-/
theorem decodeByKey_of_key {typeName : String} {maxBytes k : Nat} {byKey : Nat → Option α}
    {s : String} {x : α} (hk : stringKey? maxBytes s = some k) (hx : byKey k = some x) :
    decodeByKey typeName maxBytes byKey s = .ok x := by
  simp [decodeByKey, hk, hx]

end

end Json
