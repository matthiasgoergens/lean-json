/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser

public section

namespace Json.Parser

/-!
No object the parser returns repeats a field name, when it is told to refuse one.

This is not a property of the grammar, which admits `{"a":1,"a":2}` and leaves the outcome to the
implementation. It is a property of the machine: an object frame carries the names seen so far in
a `Std.HashSet`, and a member whose name is already there is refused. What has to be shown is
that the set really does hold every name stored in the frame, since that is what makes the
refusal cover them all.
-/

section
variable {s : String}

/--
Appending a value to a list of them keeps the key check exactly when the list already passed and
the new value passes. The machine builds an array by pushing, so what it has accumulated has to be
described one element at a time at the end of the list, where the recursive check works from the
front.

`uniqueKeysList (l ++ [v]) = true ↔ uniqueKeysList l = true ∧ uniqueKeys v = true`. The check
is a conjunction down the list, so appending amounts to conjoining once more. The equivalence
reads both ways, which is what lets it be used both to extend the property and to take it apart.
The induction is on `l`.
-/
private theorem uniqueKeysList_concat (l : List Json) (v : Json) :
    uniqueKeysList (l ++ [v]) = true ↔ uniqueKeysList l = true ∧ uniqueKeys v = true := by
  induction l with
  | nil => simp [uniqueKeysList]
  | cons _ _ ih => simp [uniqueKeysList, ih, and_assoc]

/--
Appending a field to a list of them keeps the recursive key check exactly when the list already
passed and the new field's value passes. This looks only inside the values; whether the names
themselves repeat is `distinctNames`' business and is carried alongside.

`uniqueKeysFields (l ++ [m]) = true ↔ uniqueKeysFields l = true ∧ uniqueKeys m.2 = true`. Only
`m.2` appears, the name `m.1` playing no part on either side. As with the list case the
equivalence reads both ways, and the induction is on `l`.
-/
private theorem uniqueKeysFields_concat (l : List (String × Json)) (m : String × Json) :
    uniqueKeysFields (l ++ [m]) = true ↔ uniqueKeysFields l = true ∧ uniqueKeys m.2 = true := by
  induction l with
  | nil => simp [uniqueKeysFields]
  | cons _ _ ih => simp [uniqueKeysFields, ih, and_assoc]

/-- What an object frame's fields and its set of names seen must satisfy. -/
private def FieldsOk (fields : Array (String × Json)) (seen : Std.HashSet String) : Prop :=
  uniqueKeysFields fields.toList = true ∧ distinctNames fields = true ∧
    ∀ k ∈ fieldNames fields, seen.contains k = true

private def FrameOk : Frame → Prop
  | .arr elems => uniqueKeysList elems.toList = true
  | .obj fields seen name =>
    FieldsOk fields seen ∧ findLast? fields name = none ∧ seen.contains name = true

private def StackOk (stack : List Frame) : Prop := ∀ f ∈ stack, FrameOk f

/--
A stack of frames is in good order when a frame that is itself in good order is pushed onto one
that already was. The machine pushes a frame every time it enters a container, and the invariant
has to be re-established at each push without revisiting the frames underneath.

`hf : FrameOk f` says the new frame satisfies the invariant and `hs : StackOk stack` says every
frame already there does. `StackOk` is a claim about every member of the list, so the conclusion
follows by splitting an arbitrary membership proof into the head case, which is `hf`, and the tail
case, which is `hs`.
-/
private theorem stackOk_cons {f : Frame} {stack : List Frame} (hf : FrameOk f)
    (hs : StackOk stack) : StackOk (f :: stack) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hs g hg

/--
An object frame stays in good order when a member is added, given that its name was not stored
already and its value passes the check. This is the step that does the real work: it is what turns
the machine's refusal of a repeated name into a property of the object it goes on to build.

`hfo` is the invariant on the frame so far, in three parts: its values pass the recursive check,
its names are pairwise distinct, and the set holds every name stored. `hnone` says the new name is
not among those stored, `hname` says it is in the set, and `hv` says the new value passes. The
conclusion re-establishes all three parts for the extended field array: the values through
`uniqueKeysFields_concat`, the names through `distinctNames_push`, whose second condition is
exactly `hnone`, and the set membership by cases on whether a name is the new one.
-/
private theorem fieldsOk_push {fields : Array (String × Json)} {seen : Std.HashSet String}
    {name : String} {v : Json} (hfo : FieldsOk fields seen) (hnone : findLast? fields name = none)
    (hname : seen.contains name = true) (hv : UniqueKeys v) :
    FieldsOk (fields.push (name, v)) seen := by
  obtain ⟨hu, hd, hk⟩ := hfo
  refine ⟨?_, ?_, ?_⟩
  · rw [Array.toList_push, uniqueKeysFields_concat]
    exact ⟨hu, hv⟩
  · rw [distinctNames_push]
    exact ⟨hd, hnone⟩
  · intro k hkm
    rw [fieldNames_push] at hkm
    rcases List.mem_append.mp hkm with h | h
    · exact hk k h
    · simp only [List.mem_singleton] at h
      rw [h]
      exact hname

/--
An object with no fields repeats no name. It is where the invariant starts, both for the `{}` the
machine returns outright and for a frame it has just opened.

`distinctNames (#[] : Array (String × α)) = true` holds at every value type `α`, nothing about
the values being involved. Through `distinctNames_iff` it is `Nodup` of the empty list of names,
which holds with nothing to check.
-/
private theorem distinctNames_empty {α : Type u} :
    distinctNames (#[] : Array (String × α)) = true := by
  rw [distinctNames_iff]
  simp [fieldNames]

/--
The empty object passes the key check. The machine returns `{}` on seeing `{}` in the text without
ever opening a frame, so that path has to establish the property directly rather than by cashing
in an invariant.

`UniqueKeys (Json.obj #[])` unfolds to `distinctNames #[]` conjoined with `uniqueKeysFields []`.
The first is `distinctNames_empty`, and the second is `rfl`, the recursive check on an empty list
of fields being `true` by definition.
-/
private theorem uniqueKeys_obj_empty : UniqueKeys (Json.obj (#[] : Array (String × Json))) := by
  show (distinctNames (#[] : Array (String × Json)) &&
    uniqueKeysFields (#[] : Array (String × Json)).toList) = true
  rw [distinctNames_empty]
  rfl

/--
Closing an object frame after its last member yields an object that passes the key check. This is
where the frame invariant is cashed in: the machine holds a field array and a set of names, and
what it has to produce is the property stated about the finished value.

The hypotheses are those of `fieldsOk_push`: the invariant on the frame, the new name being
unstored, that name being in the set, and the new value passing. The conclusion,
`UniqueKeys (.obj (fields.push (name, v)))`, unfolds to `distinctNames` on the extended array
conjoined with `uniqueKeysFields` on its values, both of which come from `fieldsOk_push`; its
third part, about the set, is discarded here, the finished object carrying no set.
-/
private theorem uniqueKeys_obj_push {fields : Array (String × Json)} {seen : Std.HashSet String}
    {name : String} {v : Json} (hfo : FieldsOk fields seen) (hnone : findLast? fields name = none)
    (hname : seen.contains name = true) (hv : UniqueKeys v) :
    UniqueKeys (.obj (fields.push (name, v))) := by
  obtain ⟨hu, hd, -⟩ := fieldsOk_push hfo hnone hname hv
  show (distinctNames (fields.push (name, v)) &&
    uniqueKeysFields (fields.push (name, v)).toList) = true
  rw [hu, hd]
  rfl

private def ValueKeys (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (stack : List Frame) (j : Json) (rp : s.Pos),
    value cfg p depth stack = .ok (j, rp) → StackOk stack → UniqueKeys j

private def ContinueKeys (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (v : Json) (depth : Nat) (stack : List Frame) (j : Json) (rp : s.Pos),
    continueWith cfg v p depth stack = .ok (j, rp) → UniqueKeys v → StackOk stack → UniqueKeys j

private def MemberKeys (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (fields : Array (String × Json)) (seen : Std.HashSet String)
      (stack : List Frame) (j : Json) (rp : s.Pos),
    member cfg p depth fields seen stack = .ok (j, rp) → FieldsOk fields seen →
      StackOk stack → UniqueKeys j

/--
Every value the machine returns passes the key check, at any point in its run and with any stack
of frames, provided the configuration refuses duplicates and the stack is in good order. `value`,
`continueWith` and `member` call one another, so none of them can be described alone; this is the
statement that can be proved of all three at once, and the entry points below are instances of it.

`hcfg` fixes the configuration to `.reject`, which is what makes the machine's duplicate test
actually refuse; without it the machine stores the repeated name and the conclusion fails. `n`
bounds the bytes remaining and the induction runs on `n`, the three functions recursing on that
measure rather than structurally. Each conjunct says that where the corresponding function
succeeds, and what it was handed satisfies its own invariant, the value it returns satisfies
`UniqueKeys`: `ValueKeys` asks for `StackOk`, `ContinueKeys` asks in addition that the value in
hand passes, and `MemberKeys` asks for `FieldsOk` of the frame under construction. The bound
cannot empty the claim, every position satisfying it at `n` equal to its own remaining bytes.
-/
private theorem machine_keys (cfg : Config) (hcfg : cfg.duplicateKeys = .reject) :
    ∀ (n : Nat) (p : s.Pos), p.remainingBytes ≤ n →
      ValueKeys cfg p ∧ ContinueKeys cfg p ∧ MemberKeys cfg p := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · intro depth stack j rp
      fun_cases value cfg p depth stack with
      | case1 => intro h; simp at h
      | case2 q hc _ r hr _ =>
        intro h hst
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        exact (ih _ hlt r (Nat.le_refl _)).2.1 .null depth stack j rp h rfl hst
      | case3 => intro h; simp at h
      | case4 q hc _ r hr _ =>
        intro h hst
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        exact (ih _ hlt r (Nat.le_refl _)).2.1 (.bool true) depth stack j rp h rfl hst
      | case5 => intro h; simp at h
      | case6 q hc _ r hr _ =>
        intro h hst
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        exact (ih _ hlt r (Nat.le_refl _)).2.1 (.bool false) depth stack j rp h rfl hst
      | case7 => intro h; simp at h
      | case8 => intro h; simp at h
      | case9 q hc text r hr _ =>
        intro h hst
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        exact (ih _ hlt r (Nat.le_refl _)).2.1 (.str text) depth stack j rp h rfl hst
      | case10 => intro h; simp at h
      | case11 q hc _ _ w hw _ after hb =>
        intro h hst
        have hlt : after.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        exact (ih _ hlt after (Nat.le_refl _)).2.1 (.arr #[]) depth stack j rp h rfl hst
      | case12 q hc _ _ w hw _ _ =>
        intro h hst
        have hlt : w.remainingBytes < n := by have := step?_lt hc; omega
        exact (ih _ hlt w (Nat.le_refl _)).1 (depth + 1) (.arr #[] :: stack) j rp h
          (stackOk_cons rfl hst)
      | case13 => intro h; simp at h
      | case14 q hc _ _ w hw _ after hb =>
        intro h hst
        have hlt : after.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        exact (ih _ hlt after (Nat.le_refl _)).2.1 (.obj #[]) depth stack j rp h
          uniqueKeys_obj_empty hst
      | case15 q hc _ _ w hw _ _ =>
        intro h hst
        have hlt : w.remainingBytes < n := by have := step?_lt hc; omega
        refine (ih _ hlt w (Nat.le_refl _)).2.2 (depth + 1) #[] ∅ stack j rp h ?_ hst
        exact ⟨rfl, distinctNames_empty, by simp [fieldNames]⟩
      | case16 => intro h; simp at h
      | case17 _ _ _ _ _ _ _ _ hc _ m r hr _ =>
        intro h hst
        have hlt : r.remainingBytes < n := by omega
        exact (ih _ hlt r (Nat.le_refl _)).2.1 (.num m) depth stack j rp h rfl hst
      | case18 => intro h; simp at h
    · intro v depth stack j rp
      fun_cases continueWith cfg v p depth stack with
      | case1 =>
        intro h hv _
        injection h with h
        injection h with hj _
        rw [← hj]
        exact hv
      | case2 elems outer _ w hw _ after hb _ w₂ hw₂ _ =>
        intro h hv hst
        have hlt : w₂.remainingBytes < n := by have := step?_lt hb; omega
        refine (ih _ hlt w₂ (Nat.le_refl _)).1 depth (.arr (elems.push v) :: outer) j rp h
          (stackOk_cons ?_ fun f hf => hst f (List.mem_cons_of_mem _ hf))
        have := hst _ (List.mem_cons_self ..)
        show uniqueKeysList (elems.push v).toList = true
        rw [Array.toList_push, uniqueKeysList_concat]
        exact ⟨this, hv⟩
      | case3 elems outer _ w hw _ after hb =>
        intro h hv hst
        have hlt : after.remainingBytes < n := by have := step?_lt hb; omega
        refine (ih _ hlt after (Nat.le_refl _)).2.1 (.arr (elems.push v)) (depth - 1) outer j rp h
          ?_ fun f hf => hst f (List.mem_cons_of_mem _ hf)
        have := hst _ (List.mem_cons_self ..)
        show uniqueKeysList (elems.push v).toList = true
        rw [Array.toList_push, uniqueKeysList_concat]
        exact ⟨this, hv⟩
      | case4 => intro h; simp at h
      | case5 => intro h; simp at h
      | case6 fields seen name outer _ w hw _ after hb _ w₂ hw₂ _ =>
        intro h hv hst
        have hlt : w₂.remainingBytes < n := by have := step?_lt hb; omega
        obtain ⟨hfo, hnone, hname⟩ := hst _ (List.mem_cons_self ..)
        exact (ih _ hlt w₂ (Nat.le_refl _)).2.2 depth (fields.push (name, v)) seen outer j rp h
          (fieldsOk_push hfo hnone hname hv) fun f hf => hst f (List.mem_cons_of_mem _ hf)
      | case7 fields seen name outer _ w hw _ after hb =>
        intro h hv hst
        have hlt : after.remainingBytes < n := by have := step?_lt hb; omega
        obtain ⟨hfo, hnone, hname⟩ := hst _ (List.mem_cons_self ..)
        exact (ih _ hlt after (Nat.le_refl _)).2.1 (.obj (fields.push (name, v))) (depth - 1) outer
          j rp h (uniqueKeys_obj_push hfo hnone hname hv)
          fun f hf => hst f (List.mem_cons_of_mem _ hf)
      | case8 => intro h; simp at h
      | case9 => intro h; simp at h
    · intro depth fields seen stack j rp
      fun_cases member cfg p depth fields seen stack with
      | case1 => intro h; simp at h
      | case2 => intro h; simp at h
      | case3 q hc name k hk _ hdup _ w hw _ after hb _ w₂ hw₂ _ =>
        intro h hfo hst
        have hlt : w₂.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        have hseen : seen.contains name = false := by
          simp only [hcfg, beq_self_eq_true, Bool.true_and, Bool.not_eq_true] at hdup
          exact hdup
        have hnone : findLast? fields name = none := by
          rw [findLast?_eq_none_iff]
          intro hmem
          rw [hfo.2.2 name hmem] at hseen
          exact absurd hseen (by decide)
        refine (ih _ hlt w₂ (Nat.le_refl _)).1 depth
          (.obj fields (seen.insert name) name :: stack) j rp h (stackOk_cons ?_ hst)
        refine ⟨⟨hfo.1, hfo.2.1, fun k hk => ?_⟩, hnone, by simp⟩
        simp [Std.HashSet.contains_insert, hfo.2.2 k hk]
      | case4 => intro h; simp at h
      | case5 => intro h; simp at h
      | case6 => intro h; simp at h
      | case7 => intro h; simp at h


/-! ## Entry points -/

/--
A parse starting from a given position returns no object with a repeated name, when the
configuration refuses one. `parseFrom` is where the machine is started with an empty stack, so
this is the first point at which the invariant can be discharged rather than carried further.

`hcfg` fixes the configuration to `.reject` and `h` says the parse succeeded with the value `j`.
`UniqueKeys j` says no object anywhere in `j` repeats a name. It is `machine_keys` at the initial
call, and its `StackOk` hypothesis is discharged by the stack being empty: there is no frame to
check, so the requirement costs nothing here.
-/
theorem uniqueKeys_parseFrom {cfg : Config} {start : s.Pos} {j : Json}
    (hcfg : cfg.duplicateKeys = .reject) (h : parseFrom cfg start = .ok j) : UniqueKeys j := by
  simp only [parseFrom] at h
  split at h
  · simp at h
  · next j' p hv =>
    split at h
    · injection h with hjj
      rw [← hjj]
      exact (machine_keys cfg hcfg _ (skipWs start).pos (Nat.le_refl _)).1 0 [] j' p hv
        (by intro f hf; simp at hf)
    · simp at h

/--
Told to refuse a repeated field name, the parser returns no object that has one. This is not a
property of the grammar, which admits `{"a":1,"a":2}` and leaves the outcome to the
implementation; it is a property of this machine, and it is what discharges the `UniqueKeys`
hypothesis of the round trip for a value that came from text.

`hcfg : cfg.duplicateKeys = .reject` cannot be dropped: under `.allow` the parser returns the
repeated fields as written and the conclusion is simply false. `h` says `parse s cfg` succeeded
with `j`, and `UniqueKeys j` says no object anywhere within `j`, at any depth, repeats a name.
`parse` skips an optional byte order mark and hands over to `parseFrom`, so this is that theorem
at the position it hands over at.
-/
theorem uniqueKeys_parse {cfg : Config} {j : Json} (hcfg : cfg.duplicateKeys = .reject)
    (h : parse s cfg = .ok j) : UniqueKeys j := by
  simp only [parse] at h
  exact uniqueKeys_parseFrom hcfg h

end

end Json.Parser
