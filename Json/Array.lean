/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

/-!
Facts about arrays that Lean's own library does not carry, kept apart from the JSON they serve
because there is nothing about JSON in them.

`pushInduction` is the shape every claim about a fold takes: `Array.foldl_push` turns one step of
a fold into one step of the induction, so a lemma about `Array.foldl` is proved by saying what
one more element does to the result.
-/

namespace Array

/--
Every array is reachable from the empty one by pushing a single element at a time, so a claim
about arrays can be proved the way a claim about lists is: settle it for the empty array, then say
what one more element does to it. That is what makes the fold lemmas here and the field lemmas in
`Json.Basic` provable at all, since `Array.foldl_push` turns one step of a fold into exactly one
step of this induction.

`motive` is the claim being proved, of an arbitrary array. `empty` supplies it for `#[]`, and
`push` carries it from any `a` to `a.push x` for any element `x`; from those two the conclusion
`motive a` follows for the array `a` given. Nothing here constrains `motive`, so no array of `α`
escapes the principle.
-/
theorem pushInduction {α : Type u} {motive : Array α → Prop} (empty : motive #[])
    (push : ∀ (a : Array α) (x : α), motive a → motive (a.push x)) (a : Array α) : motive a := by
  have rev : ∀ l : List α, motive l.reverse.toArray := by
    intro l
    induction l with
    | nil => exact empty
    | cons x t ih =>
      have h : (x :: t).reverse.toArray = t.reverse.toArray.push x := by simp
      exact h ▸ push _ x ih
  simpa using rev a.toList.reverse

/--
Writing to a position that already existed does not care whether anything has since been appended,
so an update and an append can be commuted. Unpicking a fold that does both, one element at a
time, is how `dedupKeys` is reasoned about, and each step needs exactly this.

`h : i < a.size` says `i` is a position of `a` itself, not one the append created. Under it,
`(a.push x).setIfInBounds i y`, appending and then writing, equals `(a.setIfInBounds i y).push x`,
writing and then appending. The hypothesis is what keeps the two sides together: at `i = a.size`
the left-hand write would land on `x` and the right-hand one would fall out of bounds.
-/
theorem setIfInBounds_push_lt {a : Array α} {i : Nat} (h : i < a.size) (x y : α) :
    (a.push x).setIfInBounds i y = (a.setIfInBounds i y).push x := by
  rw [← Array.toList_inj]
  simp [Array.toList_setIfInBounds,
    List.set_append_left _ _ (by rw [Array.length_toList]; exact h)]

/--
Writing to the position an append has just filled overwrites what was appended and nothing else,
so pushing a value and then correcting it is the same as having pushed the corrected value. This
is the case `setIfInBounds_push_lt` has to exclude.

`(a.push x).setIfInBounds a.size y` writes `y` at index `a.size`, which is where `push` put `x`,
and the result is `a.push y`. Since `a.push x` has size `a.size + 1`, that index is in bounds, so
the equation is about a write that happens rather than one `setIfInBounds` silently discards.
-/
theorem setIfInBounds_push_size {a : Array α} (x y : α) :
    (a.push x).setIfInBounds a.size y = a.push y := by
  rw [← Array.toList_inj]
  simp [Array.toList_setIfInBounds, List.set_append_right]

/--
Writing an element back where it was read leaves the array as it was. An update is often known
only by the index it targets and the value it stores, and this is what lets such an update be
recognised as no change at all, which is how `Json.setIfInBounds_self` reads a field write that
stores the field already there.

`h : i < a.size` is what gives `i` a value `a[i]`, and `a.setIfInBounds i a[i] = a` says storing
that value back at `i` returns the original array. The bound is needed to form `a[i]` in the first
place, so the claim cannot be met by `setIfInBounds` ignoring an out-of-range index.
-/
theorem setIfInBounds_getElem {a : Array α} {i : Nat} (h : i < a.size) :
    a.setIfInBounds i a[i] = a := by
  have h' : i < a.toList.length := by simpa using h
  rw [← Array.toList_inj, Array.toList_setIfInBounds, ← Array.getElem_toList h',
    List.set_getElem_self]

end Array
