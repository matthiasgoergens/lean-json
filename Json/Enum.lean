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

/--
A lookup from key to value that compares the key only with the keys of the values it holds,
computed by `keyOf`, so that whatever it finds has the key it was asked for.
-/
inductive KeyTree (α : Type u) where
  | empty
  | leaf (x : α)
  /-- Keys below `pivot` on the left, the rest on the right. -/
  | node (pivot : Nat) (below rest : KeyTree α)

/-- The value held under `k`, if any. -/
def KeyTree.find? (keyOf : α → Nat) (k : Nat) : KeyTree α → Option α
  | empty => none
  | leaf x => bif Nat.beq k (keyOf x) then some x else none
  | node pivot below rest => bif Nat.blt k pivot then below.find? keyOf k else rest.find? keyOf k

/--
Whatever the tree finds under a key has that key, whatever the tree's shape. This is what makes
the decoder accept only members' own strings, with no proof about the particular tree.

`t.find? keyOf k = some x` says the lookup of `k` reached a leaf holding `x`; `k = keyOf x` says
`k` is `x`'s key. The leaf compares `k` with `keyOf x` before answering, and a node only chooses a
side, so the conclusion holds for any pivots, sorted or not.
-/
theorem KeyTree.find?_eq_some {keyOf : α → Nat} {k : Nat} {x : α} :
    ∀ {t : KeyTree α}, t.find? keyOf k = some x → k = keyOf x
  | .empty, h => nomatch h
  | .leaf y, h => by
    simp only [find?] at h
    cases hk : Nat.beq k (keyOf y) <;> simp [hk] at h
    subst h; exact Nat.eq_of_beq_eq_true hk
  | .node pivot below rest, h => by
    simp only [find?] at h
    cases hb : Nat.blt k pivot <;> rw [hb] at h
    · exact find?_eq_some h
    · exact find?_eq_some h

private def keyRev : List UInt8 → Nat
  | [] => 0
  | b :: rest => keyRev rest * 257 + b.toNat + 1

private theorem foldl_eq_keyRev (l : List UInt8) :
    l.foldl (fun acc b => acc * 257 + b.toNat + 1) 0 = keyRev l.reverse := by
  rw [List.foldl_eq_foldr_reverse]
  induction l.reverse with
  | nil => rfl
  | cons b rest ih => simp [List.foldr, keyRev, ih]

private theorem keyRev_injective : ∀ {l₁ l₂ : List UInt8}, keyRev l₁ = keyRev l₂ → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [keyRev] at h
  | b₁ :: l₁, b₂ :: l₂, h => by
    simp only [keyRev] at h
    have h₁ := b₁.toNat_lt
    have h₂ := b₂.toNat_lt
    have hb : b₁.toNat = b₂.toNat := by omega
    have hl : keyRev l₁ = keyRev l₂ := by omega
    rw [keyRev_injective hl, UInt8.toNat_inj.mp hb]

/--
Two strings with the same key are the same string, so a key found for a text identifies the text.
It is the fact that lets the decoder compare numbers instead of strings without accepting a string
that is not a member's.

`stringKey? maxBytes s = some k` and the same for `t` say both strings are within the bound and
have key `k`; the conclusion is equality of strings. The key reads the bytes as base 257 digits,
none of them zero, so the number fixes the bytes, and the bytes fix the string.
-/
theorem stringKey?_injective {maxBytes k : Nat} {s t : String}
    (hs : stringKey? maxBytes s = some k) (ht : stringKey? maxBytes t = some k) : s = t := by
  unfold stringKey? at hs ht
  split at hs <;> split at ht <;> simp only [Option.some.injEq, reduceCtorEq] at hs ht
  rw [foldl_eq_keyRev, ← ht, foldl_eq_keyRev] at hs
  have h := List.reverse_inj.mp (keyRev_injective hs)
  rcases s with ⟨⟨⟨ls⟩⟩, _⟩
  rcases t with ⟨⟨⟨lt⟩⟩, _⟩
  simp only at h
  subst h
  rfl

/--
An enumeration's decoder accepts only the encoding of what it returns: given the key of each
member's string, whatever it decodes `j` to was written as `j`. With the round trip this makes the
codec a bijection between members and their strings.

`hkey` says each member's string is within the bound and has the key the tree compares it under.
`h` says the decoder, a string read through the tree, accepted `j` as `x`; the conclusion says `j`
is the string of `x`. `j` must be a string to be accepted, its key is `x`'s by
`KeyTree.find?_eq_some`, and equal keys mean equal strings by `stringKey?_injective`.
-/
theorem enumFromJson?_sound {typeName : String} {maxBytes : Nat} {keyOf : α → Nat}
    {toString : α → String} {t : KeyTree α}
    (hkey : ∀ x, stringKey? maxBytes (toString x) = some (keyOf x)) {j : Json} {x : α}
    (h : enumFromJson? typeName (decodeByKey typeName maxBytes (t.find? keyOf)) j = .ok x) :
    j = str (toString x) := by
  cases j with
  | str s =>
    simp only [enumFromJson?, decodeByKey] at h
    cases hk : stringKey? maxBytes s with
    | none => simp [hk] at h
    | some k =>
      cases hf : t.find? keyOf k with
      | none => simp [hk, hf] at h
      | some y =>
        simp only [hk, hf, Option.bind_some, Except.ok.injEq] at h
        subst h
        rw [KeyTree.find?_eq_some hf] at hk
        rw [stringKey?_injective hk (hkey y)]
  | _ => simp [enumFromJson?] at h

end

end Json
