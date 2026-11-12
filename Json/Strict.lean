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

/-!
Objects refused for a key their type does not know, which a derived decoder does under
`@[json_keys strict]`. The derived round trip needs the check to pass on the encoder's output, and
`checkKnownKeys_mkObj` gives that from one fact per part of the object, each proved by a lemma that
looks at no string, so the proof grows with the number of fields and not with their square.
-/

/-- The first key of an object that is not in `known`; nothing for any other value. -/
def unknownKey? (known : List String) : Json → Option String
  | obj fields => (fields.find? fun f => !known.contains f.1).map Prod.fst
  | _ => none

/-- Refuses an object holding a key outside `known`, naming the type and the key. -/
def checkKnownKeys (typeName : String) (known : List String) (j : Json) : Except String Unit :=
  match unknownKey? known j with
  | some k => .error s!"no field of {typeName} is written {compress (str k)}"
  | none => .ok ()

/--
The parts of an encoded object matched with keys one for one, every pair in a part under its key.
A derived encoder's parts are single pairs and `opt` parts, which `keyed_single` and `keyed_opt`
cover.
-/
inductive PartsKeyed : List (List (String × Json)) → List String → Prop
  | nil : PartsKeyed [] []
  | cons {p : List (String × Json)} {k : String} {ps ks} :
    (∀ q ∈ p, q.1 = k) → PartsKeyed ps ks → PartsKeyed (p :: ps) (k :: ks)

/--
A required field's part is under its own key. It is one step of the proof that a strict decoder
accepts its encoder's output, and needs no comparison of strings.

`∀ q ∈ [(k, v)], q.1 = k` says every pair of the part, which is the single pair `(k, v)`, has the
key `k`, whatever the value `v`.
-/
theorem keyed_single {k : String} {v : Json} : ∀ q ∈ [(k, v)], q.1 = k := by
  simp

/--
An optional field's part is under its own key, whether or not the field is present. It is the
counterpart of `keyed_single` for a part that may be empty.

`∀ q ∈ opt k o, q.1 = k` says every pair of the part has the key `k`: there is none when `o` is
`none`, and the single pair `(k, toJson v)` when it is `some v`.
-/
theorem keyed_opt [ToJson α] {k : String} {o : Option α} : ∀ q ∈ opt k o, q.1 = k := by
  cases o <;> simp [opt]

/--
Parts matched with keys carry no key outside those keys. It turns the one-for-one match into the
membership that `checkKnownKeys` asks about.

`PartsKeyed parts known` pairs each part with a key of `known` and says the part's pairs are under
it; the conclusion says the key of every pair `q` of every part `p` is somewhere in `known`.
-/
theorem PartsKeyed.mem {parts : List (List (String × Json))} {known : List String}
    (h : PartsKeyed parts known) : ∀ p ∈ parts, ∀ q ∈ p, q.1 ∈ known := by
  induction h with
  | nil => simp
  | cons hp _ ih =>
    intro p' hp' q hq
    rcases List.mem_cons.1 hp' with rfl | hp'
    · simp [hp q hq]
    · exact List.mem_cons_of_mem _ (ih p' hp' q hq)

/--
A strict decoder's check passes on any object built from parts that are each under their own key
of the known list. It is what lets the round trip of a strict structure be derived as for any
other: the encoder writes only the keys the decoder knows.

`h : PartsKeyed parts known` matches the encoder's parts with the keys one for one, each part's
pairs under its key. The conclusion is that `checkKnownKeys` answers `.ok ()` for the object
`mkObj parts.flatten`, whatever type name it would have reported.
-/
theorem checkKnownKeys_mkObj {typeName : String} {parts : List (List (String × Json))}
    {known : List String} (h : PartsKeyed parts known) :
    checkKnownKeys typeName known (mkObj parts.flatten) = .ok () := by
  have hnone : unknownKey? known (mkObj parts.flatten) = none := by
    simp only [unknownKey?, mkObj, Option.map_eq_none_iff, Array.find?_eq_none, List.mem_toArray,
      List.mem_flatten, Bool.not_eq_true', Bool.not_eq_false, List.contains_iff_mem]
    rintro q ⟨p, hp, hq⟩
    exact h.mem p hp q hq
  simp [checkKnownKeys, hnone]

end

end Json
