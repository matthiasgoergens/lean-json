/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.FromTo

public section

namespace Json

@[expose] section

/-!
Reaching into a value along a path.

Every operation here recurses along the path rather than through the value, so what it costs is
the length of the path, and a deeply nested document is no more dangerous than a flat one.

`set?` adds a field named by the last step of a path, since that is how an object gets built up,
but refuses a missing intermediate rather than inventing one: guessing whether a gap should
become an object or an array is how a typo turns into a new field. `remove?` closes the gap it
leaves in an array, so the index removed is occupied again by its successor.
-/

/-- One step into a value: a field of an object, or a position in an array. -/
inductive Step where
  | field (name : String)
  | index (i : Nat)
deriving DecidableEq, Repr, Inhabited

/--
Where a value sits inside another. Every operation here recurses along the path rather than
through the value, so the depth reached is the length of the path the caller wrote, whatever
the value it is applied to.
-/
abbrev Path := List Step

instance : Coe String Step := ⟨.field⟩
instance : Coe Nat Step := ⟨.index⟩

/-- The value at `p`, if there is one. Duplicate field names resolve to the last, as elsewhere. -/
def get? (j : Json) (p : Path) : Option Json :=
  match p, j with
  | [], _ => some j
  | .field k :: rest, obj fields =>
    match findLast? fields k with
    | some child => get? child rest
    | none => none
  | .index i :: rest, arr elems =>
    match elems[i]? with
    | some child => get? child rest
    | none => none
  | _, _ => none

def getD (j : Json) (p : Path) (fallback : Json) : Json := (j.get? p).getD fallback

def has (j : Json) (p : Path) : Bool := (j.get? p).isSome

/-- The value at `p`, decoded. -/
def getAs? (j : Json) (α : Type u) [FromJson α] (p : Path) : Except String α :=
  match j.get? p with
  | some v => fromJson? v
  | none => .error s!"no value at {repr p}"

/--
`j` with `v` at `p`.

A field named by the last step of the path is added when it is missing, so building an object up
one field at a time works; anything else missing along the way is an error rather than a silent
creation, since guessing whether a gap should become an object or an array is how a typo turns
into a new field.
-/
def set? (j : Json) (p : Path) (v : Json) : Except String Json :=
  match p, j with
  | [], _ => .ok v
  | .field k :: rest, obj fields =>
    match findLast? fields k with
    | some child => do
      let child ← set? child rest v
      (obj fields).setObjVal? k child
    | none =>
      match rest with
      | [] => .ok (obj (fields.push (k, v)))
      | _ => .error s!"no such field: {k}"
  | .index i :: rest, arr elems =>
    match elems[i]? with
    | some child => do
      let child ← set? child rest v
      .ok (arr (elems.setIfInBounds i child))
    | none => .error s!"index out of bounds: {i}"
  | .field _ :: _, _ => .error "expected an object"
  | .index _ :: _, _ => .error "expected an array"

def setAs? (j : Json) {α : Type u} [ToJson α] (p : Path) (v : α) : Except String Json :=
  j.set? p (toJson v)

/-- `j` with the value at `p` replaced by `f` applied to it. -/
def modify? (j : Json) (p : Path) (f : Json → Json) : Except String Json :=
  match j.get? p with
  | some v => j.set? p (f v)
  | none => .error s!"no value at {repr p}"

/--
`j` without whatever is at `p`. Every field of that name goes, which matters only for a value
that was parsed with duplicates allowed.
-/
def remove? (j : Json) (p : Path) : Except String Json :=
  match p, j with
  | [], _ => .error "the empty path names the whole value, which cannot be removed"
  | [.field k], obj fields => .ok (obj (fields.filter fun (name, _) => name != k))
  | [.index i], arr elems =>
    if i < elems.size then .ok (arr (elems.eraseIdxIfInBounds i))
    else .error s!"index out of bounds: {i}"
  | .field k :: rest, obj fields =>
    match findLast? fields k with
    | some child => do
      let child ← remove? child rest
      (obj fields).setObjVal? k child
    | none => .error s!"no such field: {k}"
  | .index i :: rest, arr elems =>
    match elems[i]? with
    | some child => do
      let child ← remove? child rest
      .ok (arr (elems.setIfInBounds i child))
    | none => .error s!"index out of bounds: {i}"
  | .field _ :: _, _ => .error "expected an object"
  | .index _ :: _, _ => .error "expected an array"

/-! ## Laws

What the two claims come down to, once the recursion over the path is peeled away, is what a fold
over an object's fields does, which the lemmas in `Json.Basic` say.
-/

/--
Whatever `set?` reports having stored is what a subsequent read of the same path finds. Without
this, a success could mean the value went somewhere else along the way, or nowhere at all, and
nothing about the interface would say so.

`j.set? p v = .ok j'` is the hypothesis that storing `v` at `p` in `j` succeeded and produced
`j'`; `j'.get? p = some v` says reading `p` out of `j'` finds a value and that value is `v`.
`get?` answers `some` only when every step of the path exists in the value it is walking, so the
conclusion also says the path is still reachable in the result. Since `set?` appends a final field
that was missing, the claim covers building a field as well as replacing one.
-/
theorem get?_set? : ∀ (p : Path) (j v j' : Json), j.set? p v = .ok j' → j'.get? p = some v := by
  intro p
  induction p with
  | nil =>
    intro j v j' h
    replace h : v = j' := by injection h
    subst h
    rfl
  | cons s rest ih =>
    intro j v j' h
    cases s with
    | field k =>
      cases j with
      | obj fields =>
        unfold set? at h
        cases hf : findLast? fields k with
        | none =>
          cases rest with
          | cons _ _ =>
            simp only [hf] at h
            replace h : (Except.error s!"no such field: {k}" : Except String Json) = .ok j' := h
            simp at h
          | nil =>
            simp only [hf] at h
            replace h : obj (fields.push (k, v)) = j' := by injection h
            subst h
            rw [get?, findLast?_push]
            simp [get?]
        | some child =>
          simp only [hf] at h
          cases hc : child.set? rest v with
          | error e =>
            rw [hc] at h
            replace h : (Except.error e : Except String Json) = .ok j' := h
            simp at h
          | ok child' =>
            obtain ⟨i, hi⟩ := findLastIdx?_isSome hf
            rw [hc] at h
            replace h : (obj fields).setObjVal? k child' = .ok j' := h
            rw [setObjVal?] at h
            simp only [hi] at h
            replace h : obj (fields.setIfInBounds i (k, child')) = j' := by injection h
            subst h
            rw [get?, findLast?_setIfInBounds hi]
            simpa using ih child v child' hc
      | null | bool _ | num _ | str _ | arr _ => simp [set?] at h
    | index i =>
      cases j with
      | arr elems =>
        unfold set? at h
        cases he : elems[i]? with
        | none =>
          simp only [he] at h
          replace h : (Except.error s!"index out of bounds: {i}" : Except String Json) = .ok j' := h
          simp at h
        | some child =>
          simp only [he] at h
          cases hc : child.set? rest v with
          | error e =>
            rw [hc] at h
            replace h : (Except.error e : Except String Json) = .ok j' := h
            simp at h
          | ok child' =>
            rw [hc] at h
            replace h : arr (elems.setIfInBounds i child') = j' := by injection h
            subst h
            have hlt : i < elems.size := (Array.getElem?_eq_some_iff.mp he).1
            rw [get?, Array.getElem?_setIfInBounds]
            simp only [hlt, ite_true]
            simpa using ih child v child' hc
      | null | bool _ | num _ | str _ | obj _ => simp [set?] at h

/--
Storing back the value already at a path leaves the whole document alone, not merely the value at
that path. That is what makes `set?` a targeted edit: it does not reorder fields, collapse a
repeated name, or otherwise disturb what it walked through on the way.

`j.get? p = some v` says `p` reaches a value in `j` and that value is `v`. The conclusion
`j.set? p v = .ok j` says storing that same `v` back at `p` succeeds and returns `j` itself, equal
as a term, so array order and duplicate field names survive. The hypothesis is what makes the
success part hold: reading found every step of the path, so none of the cases in which `set?`
reports a missing intermediate can apply.
-/
theorem set?_get? : ∀ (p : Path) (j v : Json), j.get? p = some v → j.set? p v = .ok j := by
  intro p
  induction p with
  | nil =>
    intro j v h
    replace h : j = v := by injection h
    subst h
    rfl
  | cons s rest ih =>
    intro j v h
    cases s with
    | field k =>
      cases j with
      | obj fields =>
        rw [get?] at h
        cases hf : findLast? fields k with
        | none => simp only [hf] at h; simp at h
        | some child =>
          simp only [hf] at h
          obtain ⟨i, hi⟩ := findLastIdx?_isSome hf
          unfold set?
          simp only [hf]
          rw [ih child v h]
          show (obj fields).setObjVal? k child = .ok (obj fields)
          rw [setObjVal?]
          simp only [hi, setIfInBounds_self hi hf]
      | null | bool _ | num _ | str _ | arr _ => simp [get?] at h
    | index i =>
      cases j with
      | arr elems =>
        rw [get?] at h
        cases he : elems[i]? with
        | none => simp only [he] at h; simp at h
        | some child =>
          simp only [he] at h
          obtain ⟨hlt, hget⟩ := Array.getElem?_eq_some_iff.mp he
          unfold set?
          simp only [he]
          rw [ih child v h]
          show Except.ok (arr (elems.setIfInBounds i child)) = .ok (arr elems)
          rw [← hget, Array.setIfInBounds_getElem hlt]
      | null | bool _ | num _ | str _ | obj _ => simp [get?] at h

end

end Json
