/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec
public import Json.Spec.Length

public section

namespace Json.Spec

/-!
Every number in a value the grammar derives is canonical.

`number` in the ABNF is a spelling rather than a value, and one value has many spellings: `1`,
`1.0` and `1e0` are the same number. The grammar records what the digits denote, in the one
canonical form, so a value derived from a text carries no other. That is what makes `==`,
`compare` and `hash` agree on everything a parse produces, since agreement is what
`Number.eqv_iff_eq` gives for canonical numbers and nothing weaker.
-/

/--
A number the grammar derives is in canonical form. The ABNF's `number` is a spelling, and one
number has many spellings, so without this two texts denoting the same number could yield
`Number`s that `==` calls different, and every claim about reading a value back would be a claim
about spellings rather than about numbers.

`h : Num s n r` says the front of `s` is a `number` production denoting `n`, leaving `r`; the
conclusion `n.Canonical` says `n` is the one representative its numeric value has. `Num` has a
single constructor, whose recorded value is `Number.normalize` applied to the mantissa and
exponent the digits give, and `Number.canonical_normalize` says everything `normalize` returns is
canonical, so no derivation escapes, whatever `s` and `r` are.
-/
theorem canonical_of_num {s : List Char} {n : Number} {r : List Char} (h : Num s n r) :
    n.Canonical := by
  cases h with
  | mk => exact Number.canonical_normalize _ _

/--
Every value the grammar derives holds canonical numbers throughout, not merely at the top. The six
productions are mutually recursive, so none of them can be proved on its own; this is the
induction that proves them together, and the two theorems below are the parts of it the rest of
the library uses.

`n` bounds the length of the text, by `hs : s.length ≤ n`, and the induction runs on `n`, since
the productions recurse into shorter texts rather than into structurally smaller derivations. Each
conjunct says the same thing of one production: from a derivation starting at `s`, the value it
yields answers `true` to `canonicalNumbers`, or to `canonicalNumbersList` or
`canonicalNumbersFields` where the production yields several. The bound cannot empty the
statement, since `n := s.length` satisfies `hs` for every `s`, which is how it is applied below.
-/
private theorem family_canonical : ∀ (n : Nat) (s : List Char), s.length ≤ n →
    (∀ {e r}, Arr s e r → canonicalNumbersList e.toList = true) ∧
    (∀ {f r}, Object s f r → canonicalNumbersFields f.toList = true) ∧
    (∀ {j r}, Value s j r → canonicalNumbers j = true) ∧
    (∀ {vs r}, Elements s vs r → canonicalNumbersList vs = true) ∧
    (∀ {m r}, Member s m r → canonicalNumbers m.2 = true) ∧
    (∀ {ms r}, Members s ms r → canonicalNumbersFields ms = true) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs
    have harr : ∀ {e r}, Arr s e r → canonicalNumbersList e.toList = true := by
      intro e r h
      cases h with
      | empty => rfl
      | items hb hel _ =>
        have := token_length hb
        simpa using (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.1 hel
    have hobj : ∀ {f r}, Object s f r → canonicalNumbersFields f.toList = true := by
      intro f r h
      cases h with
      | empty => rfl
      | members hb hms _ =>
        have := token_length hb
        simpa using (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.2.2 hms
    have hval : ∀ {j r}, Value s j r → canonicalNumbers j = true := by
      intro j r h
      cases h with
      | false_ => rfl
      | null => rfl
      | true_ => rfl
      | str _ => rfl
      | num hn => exact decide_eq_true (canonical_of_num hn)
      | arr ha => exact harr ha
      | obj ho => exact hobj ho
    have hels : ∀ {vs r}, Elements s vs r → canonicalNumbersList vs = true := by
      intro vs r h
      cases h with
      | one hv => simp [canonicalNumbersList, hval hv]
      | more hv hsep hel =>
        have := value_length hv
        have := token_length hsep
        have htail := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.1 hel
        simp [canonicalNumbersList, hval hv, htail]
    have hmem : ∀ {m r}, Member s m r → canonicalNumbers m.2 = true := by
      intro m r h
      cases h with
      | mk hst hsep hv =>
        have := str_length hst
        have := token_length hsep
        exact (ih _ (by omega) _ (Nat.le_refl _)).2.2.1 hv
    have hmems : ∀ {ms r}, Members s ms r → canonicalNumbersFields ms = true := by
      intro ms r h
      cases h with
      | one hm => simp [canonicalNumbersFields, hmem hm]
      | more hm hsep hms =>
        have := member_length hm
        have := token_length hsep
        have htail := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.2.2 hms
        simp [canonicalNumbersFields, hmem hm, htail]
    exact ⟨harr, hobj, hval, hels, hmem, hmems⟩

/--
A value derived from text carries canonical numbers everywhere within it, however deeply nested.
This is what lets the library treat structural equality on a parsed value as equality of what it
denotes: `Number.eqv_iff_eq` gives that for canonical numbers and for nothing weaker, so `==`,
`compare` and `hash` agree on parse results because of this and would not otherwise.

`h : Value s j r` says the front of `s` is a `value` production denoting `j`. `CanonicalNumbers j`
unfolds to `canonicalNumbers j = true`, which answers `true` when every `num` reachable in `j`,
through array elements and object fields alike, is canonical. A value holding no numbers meets
that with nothing to check, but that is one case rather than the whole content: the numbers in an
arbitrary derived value are covered too. It is `family_canonical` taken at `n := s.length`.
-/
theorem canonicalNumbers_of_value {s : List Char} {j : Json} {r : List Char} (h : Value s j r) :
    CanonicalNumbers j := (family_canonical s.length s (Nat.le_refl _)).2.2.1 h

/--
A whole JSON text yields a value whose numbers are all canonical. `Text` is the form the parser's
and the printer's own theorems are stated in, so this is the shape the round trip needs;
`compress` and `pretty` reproduce a canonical number faithfully and are not claimed to reproduce
any other.

`h : Text s j` says `s` is whitespace, then a `value` production denoting `j`, then whitespace,
with nothing left over. `CanonicalNumbers j` says every number anywhere in `j` is canonical. Only
the middle component bears on the conclusion: unfolding `Text` exposes the `Value` derivation,
which `canonicalNumbers_of_value` applies to, the surrounding whitespace contributing nothing to
`j`.
-/
theorem canonicalNumbers_of_text {s : List Char} {j : Json} (h : Text s j) :
    CanonicalNumbers j := by
  obtain ⟨a, b, hws, hv, hend⟩ := h
  exact canonicalNumbers_of_value hv

end Json.Spec
