/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Value

public section

@[expose] section

namespace Json

/-!
Walking a whole value without the C stack.

`Alg` says what to do at each kind of node, `run` applies it by recursion, and `fold` applies it
with the containers part way through held in a list. `fold_eq_run` is what lets the second stand
in for the first, so that a claim can be made against a plain recursion and still describe what
runs: `Json.Basic` ties each traversal it defines to its folded form with `csimp`.

`beqPairs` is the same idea for a comparison, which has two values to walk rather than one and so
keeps a work list of pairs rather than a stack of part-built containers.

The measures the termination arguments turn on are `noncomputable`, `sizeOf` of a `Json` being
so, and appear nowhere but in `termination_by`.
-/

/-- What a traversal does at each kind of node. -/
structure Alg (α : Type u) where
  null : α
  bool : Bool → α
  num : Number → α
  str : String → α
  arr : Array α → α
  obj : Array (String × α) → α

namespace Alg

variable {α : Type u}

mutual

/-- The algebra applied by recursion, which is the form every proof is stated against. -/
def run (a : Alg α) : Json → α
  | .null => a.null
  | .bool b => a.bool b
  | .num n => a.num n
  | .str s => a.str s
  | .arr elems => a.arr (a.runList elems.toList).toArray
  | .obj fields => a.obj (a.runFields fields.toList).toArray

def runList (a : Alg α) : List Json → List α
  | [] => []
  | j :: rest => a.run j :: a.runList rest

def runFields (a : Alg α) : List (String × Json) → List (String × α)
  | [] => []
  | (k, v) :: rest => (k, a.run v) :: a.runFields rest

end

/-- A container part way through: what has been folded already, and what is still to fold. -/
inductive Frame (α : Type u) where
  | arr (done : Array α) (rest : List Json)
  | obj (done : Array (String × α)) (name : String) (rest : List (String × Json))

noncomputable def pendingList : List Json → Nat
  | [] => 1
  | j :: rest => sizeOf j + pendingList rest + 1

noncomputable def pendingFields : List (String × Json) → Nat
  | [] => 1
  | (_, v) :: rest => sizeOf v + pendingFields rest + 1

/--
The work a list of values still to fold represents is never more than the list itself weighs. The
machine measures its progress by what is outstanding, while the recursion it replaces can only
decrease `sizeOf`, so the two measures have to be related before either descent can be shown to
terminate.

`pendingList l` counts, for every element still to fold, its `sizeOf` and one more besides, with
one for the empty list; `sizeOf l` is Lean's own structural measure. `pendingList l ≤ sizeOf l`
says the first never exceeds the second, for every list of values. The bound is tight rather than
generous: at the empty list both are one.
-/
private theorem pendingList_le : ∀ l : List Json, pendingList l ≤ sizeOf l
  | [] => by simp [pendingList]
  | j :: rest => by
    have := pendingList_le rest
    simp only [pendingList, List.cons.sizeOf_spec]
    omega

/--
The same for an object's fields: what they leave outstanding is never more than the list of them
weighs. Objects and arrays are separate constructors with separate measures, so the array case
says nothing about this one.

`pendingFields l` counts, for every field still to fold, the `sizeOf` of its value and one more,
with one for the empty list; the name contributes nothing, which is why the bound holds against
`sizeOf l`, a measure that does count it. The induction is on `l`, and each step adds at least as
much on the right as on the left.
-/
private theorem pendingFields_le : ∀ l : List (String × Json), pendingFields l ≤ sizeOf l
  | [] => by simp [pendingFields]
  | (k, v) :: rest => by
    have := pendingFields_le rest
    simp only [pendingFields, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
    omega

/--
Every value weighs something. The traversal's measure is the value in hand plus the work parked
behind it, so the step that folds a scalar and hands the answer on, entering nothing, decreases
that measure only because the scalar had a positive size to lose.

`sizeOf j` is Lean's structural measure on `Json`, and `0 < sizeOf j` says it is never zero, for
any value at all. The case that would break it is `.null`, which carries nothing; it is settled
constructor by constructor, so no shape of value is left out.
-/
private theorem sizeOf_pos (j : Json) : 0 < sizeOf j := by cases j <;> simp <;> omega

/--
Entering a non-empty array is progress. `step` descends into the first element and parks the rest
in a frame, and this says what it then holds weighs strictly less than the array it came from,
which is the whole of why that descent terminates.

`h` names the array's elements as a head `j` and a remainder `rest`. `sizeOf j + pendingList rest`
is the measure the machine holds after descending, the element in hand plus what the frame owes;
`sizeOf (Json.arr elems)` is what it held before. The inequality is strict because the array node
and its `Array` wrapper are counted on the right and on neither side of the left.
-/
private theorem arr_pending_lt {elems : Array Json} {j : Json} {rest : List Json}
    (h : elems.toList = j :: rest) : sizeOf j + pendingList rest < sizeOf (Json.arr elems) := by
  have := pendingList_le rest
  cases elems with
  | mk l => simp_all; omega

/--
Entering a non-empty object is progress, for the same reason and by the same accounting as an
array. The two are separate constructors carrying differently shaped contents, so neither case
follows from the other.

`h` names the object's fields as a head `(name, v)` and a remainder `rest`.
`sizeOf v + pendingFields rest` is what the machine holds after descending into the first value,
and `sizeOf (Json.obj fields)` what it held before. `name` is counted on the right and not on the
left, which together with the object node itself is what leaves the inequality strict.
-/
private theorem obj_pending_lt {fields : Array (String × Json)} {name : String} {v : Json}
    {rest : List (String × Json)} (h : fields.toList = (name, v) :: rest) :
    sizeOf v + pendingFields rest < sizeOf (Json.obj fields) := by
  have := pendingFields_le rest
  cases fields with
  | mk l => simp_all; omega

noncomputable def Frame.pending : Frame α → Nat
  | .arr _ rest => pendingList rest
  | .obj _ _ rest => pendingFields rest

noncomputable def pending : List (Frame α) → Nat
  | [] => 0
  | f :: k => f.pending + pending k

mutual

/-- Fold `j`, then give the answer to the frames waiting for it. -/
def step (a : Alg α) (j : Json) (k : List (Frame α)) : α :=
  match j with
  | .null => resume a a.null k
  | .bool b => resume a (a.bool b) k
  | .num n => resume a (a.num n) k
  | .str s => resume a (a.str s) k
  | .arr elems =>
    match _h : elems.toList with
    | [] => resume a (a.arr #[]) k
    | j' :: rest => step a j' (.arr #[] rest :: k)
  | .obj fields =>
    match _h : fields.toList with
    | [] => resume a (a.obj #[]) k
    | (name, v) :: rest => step a v (.obj #[] name rest :: k)
termination_by sizeOf j + pending k
decreasing_by
  · have := sizeOf_pos Json.null; omega
  · have := sizeOf_pos (Json.bool b); omega
  · have := sizeOf_pos (Json.num n); omega
  · have := sizeOf_pos (Json.str s); omega
  · have := sizeOf_pos (Json.arr elems); omega
  · have := arr_pending_lt _h; simp only [pending, Frame.pending]; omega
  · have := sizeOf_pos (Json.obj fields); omega
  · have := obj_pending_lt _h; simp only [pending, Frame.pending]; omega

/-- Give a folded value to the innermost frame, and go on to whatever that frame wants next. -/
def resume (a : Alg α) (v : α) (k : List (Frame α)) : α :=
  match k with
  | [] => v
  | .arr done rest :: k' =>
    match rest with
    | [] => resume a (a.arr (done.push v)) k'
    | j :: rest' => step a j (.arr (done.push v) rest' :: k')
  | .obj done name rest :: k' =>
    match rest with
    | [] => resume a (a.obj (done.push (name, v))) k'
    | (name', v') :: rest' => step a v' (.obj (done.push (name, v)) name' rest' :: k')
termination_by pending k
decreasing_by
  · simp only [pending, Frame.pending, pendingList]; omega
  · simp only [pending, Frame.pending, pendingList]; omega
  · simp only [pending, Frame.pending, pendingFields]; omega
  · simp only [pending, Frame.pending, pendingFields]; omega

end

/-- What the frames still owe a folded value, said by recursion. -/
private def close (a : Alg α) : α → List (Frame α) → α
  | v, [] => v
  | v, .arr done rest :: k => close a (a.arr (done.push v ++ (a.runList rest).toArray)) k
  | v, .obj done name rest :: k =>
    close a (a.obj (done.push (name, v) ++ (a.runFields rest).toArray)) k

/--
The machine with an explicit work list computes what the plain recursion computes, at every point
in its run rather than only at the start. `step` and `resume` call one another and both carry a
list of frames, so neither can be described on its own; this is the pair of claims that can be
proved together, and `fold_eq_run` is the instance of it the library uses.

`n` bounds the measure the two functions decrease, by `sizeOf j + pending k` and `pending k`
respectively, and the induction runs on `n`, since they recurse on that measure and not
structurally. The first conjunct says `step a j k`, folding `j` with the frames `k` waiting,
equals `close a (run a j) k`: what the plain recursion makes of `j`, handed to those frames. The
second says the same of `resume a v k`, where the answer `v` is already in hand. `close` states by
recursion what the frames still owe, so it is a specification rather than a second machine. The
bound empties neither claim, since any `j` and `k` satisfy it at `n` equal to their own measure.
-/
private theorem machine (a : Alg α) : ∀ n : Nat,
    (∀ (j : Json) (k : List (Frame α)), sizeOf j + pending k ≤ n →
        step a j k = close a (run a j) k) ∧
      (∀ (v : α) (k : List (Frame α)), pending k ≤ n → resume a v k = close a v k) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have H1 : ∀ (j : Json) (k : List (Frame α)), sizeOf j + pending k < n →
        step a j k = close a (run a j) k :=
      fun j k h => (ih _ h).1 j k (Nat.le_refl _)
    have H2 : ∀ (v : α) (k : List (Frame α)), pending k < n → resume a v k = close a v k :=
      fun v k h => (ih _ h).2 v k (Nat.le_refl _)
    refine ⟨?_, ?_⟩
    · intro j k hn
      have hpos := sizeOf_pos j
      cases j with
      | null => rw [step, run]; exact H2 _ _ (by omega)
      | bool b => rw [step, run]; exact H2 _ _ (by omega)
      | num x => rw [step, run]; exact H2 _ _ (by omega)
      | str s => rw [step, run]; exact H2 _ _ (by omega)
      | arr elems =>
        rw [step]
        split
        · next hl => rw [run, hl]; simp only [runList]; exact H2 _ _ (by omega)
        · next j' rest hl =>
          have hlt := arr_pending_lt hl
          rw [H1 j' _ (by simp only [pending, Frame.pending]; omega), run, hl]
          simp [close, runList]
      | obj fields =>
        rw [step]
        split
        · next hl => rw [run, hl]; simp only [runFields]; exact H2 _ _ (by omega)
        · next name v rest hl =>
          have hlt := obj_pending_lt hl
          rw [H1 v _ (by simp only [pending, Frame.pending]; omega), run, hl]
          simp [close, runFields]
    · intro v k hn
      cases k with
      | nil => rw [resume, close]
      | cons f k' =>
        cases f with
        | arr done rest =>
          cases rest with
          | nil =>
            rw [resume, close]
            refine H2 _ _ ?_
            simp only [pending, Frame.pending, pendingList] at hn ⊢
            omega
          | cons j rest' =>
            rw [resume, H1 j _ (by simp only [pending, Frame.pending, pendingList] at hn ⊢; omega),
              close]
            simp [close, runList]
        | obj done name rest =>
          cases rest with
          | nil =>
            rw [resume, close]
            refine H2 _ _ ?_
            simp only [pending, Frame.pending, pendingFields] at hn ⊢
            omega
          | cons p rest' =>
            obtain ⟨name', v'⟩ := p
            rw [resume,
              H1 v' _ (by simp only [pending, Frame.pending, pendingFields] at hn ⊢; omega), close]
            simp [close, runFields]

/-- The traversal, with its pending work in a list rather than on the stack. -/
def fold (a : Alg α) (j : Json) : α := step a j []

/--
The traversal that keeps its pending work in a list computes exactly what the plain recursion
computes. This is what the module exists for: `Json.Basic` states each of `hash`, `uniqueKeys`,
`canonicalNumbers` and `depth` as a recursion and proves things about that, then hands the
compiled program the folded form, so a value nesting a million deep costs heap and not a crash.

`fold a j` is `step a j []`, the machine started on `j` with no frame waiting; `run a j` is the
algebra applied by structural recursion. The equation is between the two results, at the algebra's
own carrier `α`, and holds for every algebra and every value with no side condition on either. It
is `machine` taken at the measure `j` itself supplies.
-/
theorem fold_eq_run (a : Alg α) (j : Json) : fold a j = run a j :=
  (machine a (sizeOf j + pending ([] : List (Frame α)))).1 j [] (Nat.le_refl _)

/--
A traversal replaces an object's values and leaves its names exactly as they were, order included.
Any claim about an object that is about its names rather than its values has to cross a traversal
somehow, and this is how: it is what carries `distinctNames` through `Alg.run`.

`runFields a l` applies the algebra to each field's value and keeps the pairs.
`(runFields a l).map (·.1)` is the names of the result and `l.map (·.1)` the names of the input,
and the equation says they are the same list, so neither a name nor its position changes. Nothing
about the algebra is used, since `runFields` never passes a name to it.
-/
theorem runFields_names (a : Alg α) : ∀ l : List (String × Json),
    (runFields a l).map (·.1) = l.map (·.1)
  | [] => rfl
  | (k, v) :: rest => by simp [runFields, runFields_names a rest]

end Alg

/-! ## Equality by work list

Comparing two values walks both at once, so there is no part-built result to keep: a list of the
pairs still to compare is the whole state.
-/

noncomputable def weight : List (Json × Json) → Nat
  | [] => 0
  | (a, _) :: rest => sizeOf a + weight rest

/-- The values of two objects, paired up by position. -/
def valuePairs (x y : Array (String × Json)) : List (Json × Json) :=
  (x.toList.map Prod.snd).zip (y.toList.map Prod.snd)

/--
Disposing of the pair at the front of a comparison's work list is progress. Most of `beqPairs`
compares two scalars and moves on, and this is why doing so terminates.

`weight` sums `sizeOf` over the left-hand value of each pair, and
`weight rest < weight ((a, b) :: rest)` says removing the head strictly reduces that sum.
Strictness rests on `sizeOf_pos`: were a value allowed to weigh nothing, dropping the pair holding
it would leave the measure where it was. `b` is not counted by `weight` at all, so the right-hand
value of the pair is unconstrained.
-/
private theorem weight_lt_cons (a b : Json) (rest : List (Json × Json)) :
    weight rest < weight ((a, b) :: rest) := by
  have := Alg.sizeOf_pos a
  simp only [weight]
  omega

/--
The work list's measure is additive, so pushing a container's members in front of what remains
costs exactly what those members weigh. Every case of `beqPairs` that descends does so by an
append, and none of them could be measured without this.

`weight (l₁ ++ l₂) = weight l₁ + weight l₂` says the sum over a concatenation splits into
the sums over its parts. The induction is on `l₁`; nothing is used beyond `weight` being a sum,
one term per pair, over the left-hand values.
-/
private theorem weight_append : ∀ l₁ l₂ : List (Json × Json),
    weight (l₁ ++ l₂) = weight l₁ + weight l₂
  | [], _ => by simp [weight]
  | (a, b) :: rest, l₂ => by
    simp only [List.cons_append, weight, weight_append rest l₂]
    omega

/--
Pairing up two arrays' elements to compare them costs strictly less than the array being entered
had outstanding. This is the array half of `beqPairs`' termination: what gets pushed weighs less
than the frame it stands in for.

`xs.zip ys` pairs elements up to the shorter of the two lists, so a short `ys` only removes pairs.
`weight` sums `sizeOf` over the left-hand values, hence over `xs` truncated to that length, while
`Alg.pendingList xs` counts every element of `xs` and one more besides, plus one for the end. The
inequality is strict at every pair of lengths, the case of an empty `ys` included, where the left
is zero and the right is at least one.
-/
private theorem weight_zip_lt : ∀ (xs ys : List Json), weight (xs.zip ys) < Alg.pendingList xs
  | [], _ => by simp [weight, Alg.pendingList]
  | _ :: _, [] => by simp [weight, Alg.pendingList]
  | x :: xs, y :: ys => by
    have := weight_zip_lt xs ys
    simp only [List.zip_cons_cons, weight, Alg.pendingList]
    omega

/--
The same for two objects' fields: pairing their values costs strictly less than the object's
fields had outstanding. Fields carry names and elements do not, so this does not follow from the
array case, though it is proved the same way.

The zip is of `xs.map Prod.snd` against `ys.map Prod.snd`, the values with the names dropped,
which is what comparing two objects actually pushes. `weight` sums `sizeOf` over the left-hand
values of the result, and `Alg.pendingFields xs` counts each of `xs`' values and one more, plus
one for the end. Truncation to the shorter list can only reduce the left, so the inequality
survives any mismatch in length.
-/
private theorem weight_zip_fields_lt : ∀ (xs ys : List (String × Json)),
    weight ((xs.map Prod.snd).zip (ys.map Prod.snd)) < Alg.pendingFields xs
  | [], _ => by simp [weight, Alg.pendingFields]
  | _ :: _, [] => by simp [weight, Alg.pendingFields]
  | (k, v) :: xs, (k', v') :: ys => by
    have := weight_zip_fields_lt xs ys
    simp only [List.map_cons, List.zip_cons_cons, weight, Alg.pendingFields]
    omega

/--
The previous bound in the form the comparison actually uses, over field arrays rather than lists
of fields. `beqPairs` pushes `valuePairs x y`, so its termination argument needs the bound stated
of exactly that.

`valuePairs x y` drops the names and zips the values of the two objects.
`Alg.pendingFields x.toList` is what the first object's fields have outstanding, `y` playing no
part in it. The inequality is `weight_zip_fields_lt` at the two arrays' lists, so it is strict for
the same reason, and unaffected by the objects differing in size.
-/
private theorem weight_valuePairs_lt (x y : Array (String × Json)) :
    weight (valuePairs x y) < Alg.pendingFields x.toList :=
  weight_zip_fields_lt x.toList y.toList

/--
An array's elements have strictly less outstanding than the array itself weighs. `beqPairs`
measures its work list by the sizes of the values in it, so descending into an array has to be
paid for out of that array's own size, and this is what says there is enough to pay with.

`Alg.pendingList elems.toList` counts each element's `sizeOf` and one more besides, with one for
the empty list; `sizeOf (Json.arr elems)` weighs the whole node. The gap is the constructor and
its `Array` wrapper, so the inequality is strict even for the empty array, where the left is one.
-/
private theorem pendingList_arr_lt (elems : Array Json) :
    Alg.pendingList elems.toList < sizeOf (Json.arr elems) := by
  have := Alg.pendingList_le elems.toList
  cases elems with
  | mk l => simp_all; omega

/--
An object's fields have strictly less outstanding than the object itself weighs, which is what
pays for descending into an object. It is the counterpart of the array bound, and needed
separately because the two constructors hold differently shaped contents.

`Alg.pendingFields fields.toList` counts each field's value and one more besides, with one for the
empty list, ignoring the names; `sizeOf (Json.obj fields)` weighs the whole node, names included.
Both the node itself and the names it holds sit in the gap, so the inequality is strict even for
an object with no fields.
-/
private theorem pendingFields_obj_lt (fields : Array (String × Json)) :
    Alg.pendingFields fields.toList < sizeOf (Json.obj fields) := by
  have := Alg.pendingFields_le fields.toList
  cases fields with
  | mk l => simp_all; omega

/-- Whether every pair in the list is equal, the members of a container joining the list. -/
def beqPairs : List (Json × Json) → Bool
  | [] => true
  | (a, b) :: rest =>
    match a, b with
    | .null, .null => beqPairs rest
    | .bool x, .bool y => x == y && beqPairs rest
    | .num x, .num y => x == y && beqPairs rest
    | .str x, .str y => x == y && beqPairs rest
    | .arr x, .arr y => x.size == y.size && beqPairs (x.toList.zip y.toList ++ rest)
    | .obj x, .obj y =>
      x.toList.map Prod.fst == y.toList.map Prod.fst && beqPairs (valuePairs x y ++ rest)
    | _, _ => false
termination_by l => weight l
decreasing_by
  all_goals
    first
      | exact weight_lt_cons _ _ _
      | (rw [weight_append]
         have := weight_zip_lt x.toList y.toList
         have := pendingList_arr_lt x
         simp only [weight]
         omega)
      | (rw [weight_append]
         have := weight_valuePairs_lt x y
         have := pendingFields_obj_lt x
         simp only [weight]
         omega)


end Json
