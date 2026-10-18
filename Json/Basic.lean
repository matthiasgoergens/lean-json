/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Array
public import Json.Number
public import Json.Fold
public import Std.Data.HashSet

public section

@[expose] section

/-!
The data model, and what can be done with it alone.

An object holds its fields in the order they were written and can hold one name twice, so that a
parsed value is a faithful image of its text. Lookup takes the last of a repeated name, as
ECMA-262 and the mainstream implementations do. Equality and hashing are structural, which is
safe here because `Json.Number` keeps one spelling of each number.

Nothing here panics: an accessor returns `Except String`, or a default where the name says so.
Each of `beq`, `hash`, `uniqueKeys`, `canonicalNumbers` and `depth` is written as a recursion,
which is the form its proofs are stated against, and paired with a `csimp` lemma that hands the
compiled program the equal traversal from `Json.Fold`, whose pending work is a list rather than
a C stack. A value that nests a million deep therefore costs heap and not a crash.
-/

namespace Json

-- Equality, hashing and the key check all recurse through the two nested `Array` positions, for
-- which no deriving handler applies. Splitting each into a mutual group over `List` keeps the
-- termination argument and the correctness proof straightforward.
mutual

def beq : Json → Json → Bool
  | null, null => true
  | bool a, bool b => a == b
  | num a, num b => a == b
  | str a, str b => a == b
  | arr a, arr b => beqList a.toList b.toList
  | obj a, obj b => beqFields a.toList b.toList
  | _, _ => false

def beqList : List Json → List Json → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false

def beqFields : List (String × Json) → List (String × Json) → Bool
  | [], [] => true
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys => k₁ == k₂ && beq v₁ v₂ && beqFields xs ys
  | _, _ => false

end

mutual

/--
Structural comparison decides equality of values: it answers `true` on exactly the pairs that are
the same term. The `DecidableEq`, `BEq` and `LawfulBEq` instances below are all this claim in
another guise, and it is only a useful notion of equality because `Json.Number` keeps one spelling
per number, so two values denoting the same document really are the same term.

`beq a b = true ↔ a = b` reads both ways: no two distinct values are called equal, and no two
equal values are called different. The proof is by cases on both arguments, so the twenty-five
mismatched pairs of constructors are dispatched alongside the six matching ones. Arrays and
objects defer to `beqList_iff_eq` and `beqFields_iff_eq`, which is why all three are proved at
once.
-/
theorem beq_iff_eq : ∀ a b : Json, beq a b = true ↔ a = b
  | null, null => by simp [beq]
  | bool _, bool _ => by simp [beq]
  | num _, num _ => by simp [beq]
  | str _, str _ => by simp [beq]
  | arr x, arr y => by simp [beq, beqList_iff_eq x.toList y.toList, Array.toList_inj]
  | obj x, obj y => by simp [beq, beqFields_iff_eq x.toList y.toList, Array.toList_inj]
  | null, bool _ | null, num _ | null, str _ | null, arr _ | null, obj _
  | bool _, null | bool _, num _ | bool _, str _ | bool _, arr _ | bool _, obj _
  | num _, null | num _, bool _ | num _, str _ | num _, arr _ | num _, obj _
  | str _, null | str _, bool _ | str _, num _ | str _, arr _ | str _, obj _
  | arr _, null | arr _, bool _ | arr _, num _ | arr _, str _ | arr _, obj _
  | obj _, null | obj _, bool _ | obj _, num _ | obj _, str _ | obj _, arr _ => by simp [beq]

/--
Comparing two lists of values position by position decides their equality. `beq` compares two
arrays through this, so it cannot be established first; the two are one mutual induction.

`beqList xs ys = true ↔ xs = ys` covers lists of unequal length as well as equal ones, since
`beqList` answers `false` as soon as one list runs out while the other has not. The element case
appeals to `beq_iff_eq`, and the whole is an induction stepping both lists together.
-/
theorem beqList_iff_eq : ∀ xs ys : List Json, beqList xs ys = true ↔ xs = ys
  | [], [] => by simp [beqList]
  | x :: xs, y :: ys => by simp [beqList, beq_iff_eq x y, beqList_iff_eq xs ys]
  | [], _ :: _ => by simp [beqList]
  | _ :: _, [] => by simp [beqList]

/--
Comparing two lists of fields decides their equality, in names, values and order together. Object
equality here is equality of the field array as written rather than of what lookup would find, so
a repeated name or a different order makes two objects different, which is what keeps a parsed
value a faithful image of its text.

`beqFields xs ys = true ↔ xs = ys` requires each pair of fields to agree in both components:
`k₁ == k₂` on the names, which is `String`'s own equality, and `beq v₁ v₂` on the values,
which `beq_iff_eq` turns into equality. Lists of unequal length are answered `false`.
-/
theorem beqFields_iff_eq : ∀ xs ys : List (String × Json), beqFields xs ys = true ↔ xs = ys
  | [], [] => by simp [beqFields]
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys => by
    simp [beqFields, beq_iff_eq v₁ v₂, beqFields_iff_eq xs ys, and_assoc]
  | [], _ :: _ => by simp [beqFields]
  | _ :: _, [] => by simp [beqFields]

end

/-! ## Walking a value without the stack

Each traversal below is written twice: as a recursion, which is what every theorem about it is
stated against, and again through `Json.Fold`, which holds its pending work in a list. A `csimp`
lemma joins the two, so what a caller reasons about and what the program runs are one function.
Comparison is the odd one out, having two values to walk and so no part-built result to carry.
-/

/--
Comparing two lists position by position is comparing their lengths and then comparing the pairs a
zip makes of them. The work-list machine pushes zipped pairs when it descends into two arrays, so
this is the shape in which its answer can be compared with the recursion's.

`xs.zip ys` truncates to the shorter list, which on its own would call `[1]` and `[1, 2]` equal;
the `xs.length == ys.length` conjunct is what rules that out. `.all` then requires `beq` to hold
of every pair. Both sides are `Bool` and the equation is between them, so the two agree on which
way a comparison fails as well as on when it succeeds.
-/
theorem beqList_zip : ∀ xs ys : List Json,
    beqList xs ys = ((xs.length == ys.length) && (xs.zip ys).all fun p => beq p.1 p.2)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [beqList, beqList_zip xs ys, List.zip_cons_cons, List.all_cons, List.length_cons]
    cases beq x y <;> simp

/--
Comparing two lists of fields is comparing their names as lists and then comparing the values a
zip pairs up. This is the object counterpart of the array case, and the form the work-list machine
leaves a pair of objects in.

`xs.map Prod.fst == ys.map Prod.fst` compares the names in order, and so settles the number of
fields as well; `((xs.map Prod.snd).zip (ys.map Prod.snd)).all` then compares the values pairwise.
No separate length check is needed, unlike the array case: two lists of names cannot be equal
without being the same length, so the zip cannot quietly truncate.
-/
theorem beqFields_zip : ∀ xs ys : List (String × Json),
    beqFields xs ys = ((xs.map Prod.fst == ys.map Prod.fst) &&
      ((xs.map Prod.snd).zip (ys.map Prod.snd)).all fun p => beq p.1 p.2)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | (k₁, v₁) :: xs, (k₂, v₂) :: ys => by
    simp only [beqFields, beqFields_zip xs ys, List.map_cons, List.zip_cons_cons, List.all_cons]
    cases beq v₁ v₂ <;> cases h : k₁ == k₂ <;> simp_all

/--
The comparison machine agrees with comparing each pair on its work list where it stands. This is
what lets `beq`, a recursion, be replaced by a function that keeps its outstanding comparisons in
a list, so comparing two values that nest a million deep costs heap rather than a C stack.

`beqPairs l` walks `l`, replacing a pair of containers by the pairs of their members;
`l.all fun p => beq p.1 p.2` compares each pair separately. The equation holds at every work list,
not merely at a singleton, which is what makes it an induction hypothesis. That induction follows
`beqPairs`' own recursion, with `beqList_zip` and `beqFields_zip` supplying the container cases,
where the pushed members have to be shown to yield the same answer as the whole.
-/
theorem beqPairs_eq (l : List (Json × Json)) : beqPairs l = l.all fun p => beq p.1 p.2 := by
  induction l using beqPairs.induct <;>
    simp_all [beqPairs, beq, List.all_append, beqList_zip, beqFields_zip, valuePairs,
      Bool.and_assoc]

def beqFold (a b : Json) : Bool := beqPairs [(a, b)]

/--
The compiler is told to run the work-list comparison in place of the recursion. Every claim above
is about `beq`, and everything executed is `beqFold`; this is what makes them the same program
rather than two that happen to agree.

`@beq = @beqFold` is an equation between the functions themselves, over every pair of values,
which is what `@[csimp]` requires before it will substitute one for the other in compiled code.
`beqFold a b` is `beqPairs [(a, b)]`, the machine on a one-pair work list, which `beqPairs_eq`
reduces to `beq a b`.
-/
@[csimp] theorem beq_eq_beqFold : @beq = @beqFold := by
  funext a b
  rw [beqFold, beqPairs_eq]
  simp

instance : DecidableEq Json := fun a b => decidable_of_iff _ (beq_iff_eq a b)

instance : BEq Json := ⟨beq⟩

instance : LawfulBEq Json where
  eq_of_beq h := (beq_iff_eq _ _).mp h
  rfl := (beq_iff_eq _ _).mpr rfl

mutual

def hash : Json → UInt64
  | null => 11
  | bool b => mixHash 13 (Hashable.hash b)
  | num n => mixHash 17 (Hashable.hash n)
  | str s => mixHash 19 (Hashable.hash s)
  | arr elems => mixHash 23 (hashList elems.toList)
  | obj fields => mixHash 29 (hashFields fields.toList)

def hashList : List Json → UInt64
  | [] => 7
  | j :: rest => mixHash (hash j) (hashList rest)

def hashFields : List (String × Json) → UInt64
  | [] => 7
  | (k, v) :: rest => mixHash (mixHash (Hashable.hash k) (hash v)) (hashFields rest)

end

def hashAlg : Alg UInt64 where
  null := 11
  bool := fun b => mixHash 13 (Hashable.hash b)
  num := fun n => mixHash 17 (Hashable.hash n)
  str := fun s => mixHash 19 (Hashable.hash s)
  arr := fun elems => mixHash 23 (elems.toList.foldr mixHash 7)
  obj := fun fields =>
    mixHash 29 (fields.toList.foldr (fun p acc => mixHash (mixHash (Hashable.hash p.1) p.2) acc) 7)

mutual

/--
The hash written as a recursion is the hash the algebra computes. `Json.Fold` knows only how to
run algebras, so this is the only route by which anything proved of `hash` reaches the stackless
traversal that actually runs.

`hash` recurses through the value, mixing a distinct tag per constructor into what the contents
hash to; `hashAlg` says the same at each node and `Alg.run` applies it by recursion. The equation
is between `UInt64`s, so it is the hash itself that agrees. Arrays and objects go through the two
companion claims, which is why the three are proved together.
-/
theorem hash_eq_run : ∀ j : Json, hash j = hashAlg.run j
  | .null => rfl
  | .bool _ => rfl
  | .num _ => rfl
  | .str _ => rfl
  | .arr elems => by rw [hash, Alg.run, hashList_eq_run]; rfl
  | .obj fields => by rw [hash, Alg.run, hashFields_eq_run]; rfl

/--
Hashing a list of values is hashing each and mixing the results right to left. The array case of
`hash` goes through this, and the mutual induction needs it in a form the algebra can be read off
rather than in `hash`'s own recursive shape.

`hashList` mixes as it recurses; on the right, `hashAlg.runList l` hashes each element and
`foldr mixHash 7` combines them. `7` is the seed for the empty list on both sides, which is what
settles the base case, and `mixHash` is not commutative, so the direction of the fold is part of
the claim rather than an incidental choice.
-/
theorem hashList_eq_run : ∀ l : List Json, hashList l = (hashAlg.runList l).foldr mixHash 7
  | [] => rfl
  | j :: rest => by
    rw [hashList, Alg.runList, List.foldr_cons, hash_eq_run j, hashList_eq_run rest]

/--
Hashing a list of fields is hashing each value, mixing its name in, and combining right to left.
The names take part, so two objects differing only in a name hash differently, and this is what
carries that into the folded form.

`hashFields` mixes `Hashable.hash k` with `hash v` for each field and then into the hash of the
rest; the right-hand side does the same over `hashAlg.runFields l`, whose names `Alg.runFields`
leaves as they were. The seed is `7` on both sides, and the fold is again right to left, so field
order is part of what is hashed.
-/
theorem hashFields_eq_run : ∀ l : List (String × Json), hashFields l =
    (hashAlg.runFields l).foldr (fun p acc => mixHash (mixHash (Hashable.hash p.1) p.2) acc) 7
  | [] => rfl
  | (k, v) :: rest => by
    rw [hashFields, Alg.runFields, List.foldr_cons, hash_eq_run v, hashFields_eq_run rest]

end

def hashFold (j : Json) : UInt64 := hashAlg.fold j

/--
The compiler runs the stackless hash. `hash` is the recursion every claim is stated against and
`hashFold` is the traversal that holds its part-built containers in a list, so hashing a deeply
nested value costs memory rather than crashing.

`@hash = @hashFold` is an equation between the functions, over every value, which is what
`@[csimp]` requires. `hashFold` is `hashAlg.fold`; `Alg.fold_eq_run` reduces that to
`hashAlg.run`, and `hash_eq_run` identifies it with `hash`.
-/
@[csimp] theorem hash_eq_hashFold : @hash = @hashFold := by
  funext j
  rw [hashFold, Alg.fold_eq_run, hash_eq_run]

instance : Hashable Json := ⟨hash⟩

def ofInt (i : Int) : Json := num (Number.ofInt i)

def ofNat (n : Nat) : Json := num (Number.ofNat n)

instance : Coe Bool Json := ⟨bool⟩
instance : Coe String Json := ⟨str⟩
instance : Coe Number Json := ⟨num⟩
instance : Coe Nat Json := ⟨ofNat⟩
instance : Coe Int Json := ⟨ofInt⟩
instance : OfNat Json n := ⟨num (Number.ofNat n)⟩

def mkObj (fields : List (String × Json)) : Json := obj fields.toArray

def isNull : Json → Bool
  | null => true
  | _ => false

-- The field helpers are polymorphic in the value type. Nothing about resolving duplicate names
-- depends on the values, and it lets them be tested at a type that has generators.

/-- The value of the last field named `k`, which is the one lookup resolves to. -/
def findLast? (fields : Array (String × α)) (k : String) : Option α :=
  fields.foldl (init := none) fun found (key, v) => if key == k then some v else found

/-- The position of the last field named `k`. -/
def findLastIdx? (fields : Array (String × α)) (k : String) : Option Nat :=
  (fields.foldl (init := ((none : Option Nat), 0)) fun (found, i) (key, _) =>
    (if key == k then some i else found, i + 1)).1

/--
Keeps one field per name, the last value at the first position that name occupied, so that
lookup is unaffected and field order is preserved as far as it can be.
-/
def dedupKeys (fields : Array (String × α)) : Array (String × α) :=
  fields.foldl (init := #[]) fun acc (k, v) =>
    match findLastIdx? acc k with
    | some i => acc.setIfInBounds i (k, v)
    | none => acc.push (k, v)

/-- Whether the field names of one object are pairwise distinct. -/
def distinctNames (fields : Array (String × α)) : Bool :=
  go 0 ∅
where
  go (i : Nat) (seen : Std.HashSet String) : Bool :=
    if h : i < fields.size then
      let k := fields[i].1
      if seen.contains k then false else go (i + 1) (seen.insert k)
    else
      true

/-- The names an object gives its fields, in the order they appear. -/
def fieldNames (a : Array (String × α)) : List String := a.toList.map (·.1)

/--
Appending a field appends its name at the end of the names. Nearly every claim about field arrays
is proved by `Array.pushInduction`, and this is the step that turns one push of a field into one
push of a name, which is what lets `Nodup` carry such an argument.

`fieldNames a` is the array's names in order. The equation puts `x.1`, the appended field's name,
at the end and leaves the earlier names untouched, which is where the field itself went. `x.2`
does not appear on either side, so nothing about the value matters.
-/
@[simp] theorem fieldNames_push (a : Array (String × α)) (x : String × α) :
    fieldNames (a.push x) = fieldNames a ++ [x.1] := by simp [fieldNames]

/--
There are exactly as many names as there are fields. Positions are found in the array and used
against the list of names, and neither can be indexed by the other's bound until the two lengths
are known to agree.

`fieldNames a` maps each field to its name, so the claim `(fieldNames a).length = a.size` is that
mapping preserves length. It holds for every array, with no condition on the names, and is what
turns a bound `i < a.size` into a bound on the name list and back.
-/
private theorem fieldNames_length (a : Array (String × α)) : (fieldNames a).length = a.size := by
  simp [fieldNames]

/--
The names from a position onwards begin with the name at that position. `distinctNames` runs as a
loop over positions while what it means is stated about a suffix of the names, and this is what
steps the one against the other.

`h : i < a.size` is what gives `a[i]` a value; without it there would be no name to peel off.
`(fieldNames a).drop i` is the names from `i` onwards, and the equation splits it into `a[i].1`
followed by the names from `i + 1` onwards, which is exactly one turn of the loop.
-/
private theorem fieldNames_drop (a : Array (String × α)) {i : Nat} (h : i < a.size) :
    (fieldNames a).drop i = a[i].1 :: (fieldNames a).drop (i + 1) := by
  have hi : i < (fieldNames a).length := by simpa [fieldNames_length] using h
  rw [List.drop_eq_getElem_cons hi]
  simp [fieldNames]

/--
The loop that looks for a repeated name is doing what its name says at every point in its run, not
merely at the start. It carries a set of names seen so far, so nothing can be said about where it
has got to without saying what that set means, and this says it.

`i` is the position reached and `seen` the names collected before it. The loop answers `true`
exactly when two things hold of the names from `i` onwards: they repeat none of one another, which
is `Nodup`; and none of them is in `seen`, so none repeats a name from before `i`. Both conjuncts
are needed, a repetition being able to straddle the boundary as well as fall on one side of it. It
is proved by the loop's own induction, whose cases are a name already seen, a fresh name, and the
end of the array.
-/
private theorem distinctNamesGo (a : Array (String × α)) (i : Nat) (seen : Std.HashSet String) :
    distinctNames.go a i seen = true ↔
      ((fieldNames a).drop i).Nodup ∧ ∀ x ∈ (fieldNames a).drop i, seen.contains x = false := by
  induction i, seen using distinctNames.go.induct (fields := a) with
  | case1 i seen h k hc =>
    rw [distinctNames.go, dite_eq_left h, ite_eq_left hc, fieldNames_drop a h]
    have hmem : a[i].1 ∈ seen := by simpa using hc
    simp [hmem]
  | case2 i seen h k hc ih =>
    rw [distinctNames.go, dite_eq_left h, ite_eq_right hc, ih, fieldNames_drop a h]
    simp only [Std.HashSet.contains_insert]
    grind
  | case3 i seen h =>
    have hnil : (fieldNames a).drop i = [] := by
      apply List.drop_eq_nil_of_le
      rw [fieldNames_length]
      omega
    rw [distinctNames.go, dite_eq_right h]
    simp [hnil]

/--
The check for repeated field names answers `true` exactly when the names are pairwise distinct.
`uniqueKeys` is read through this, and the parser's rejection of duplicates is stated against it,
so a `Bool` computed by a hash-set loop has to be tied to the mathematical property before either
can be believed.

`(fieldNames a).Nodup` says no name appears twice anywhere in the array. The equivalence is
`distinctNamesGo` taken at `i = 0` with an empty `seen`, where the suffix is the whole name list
and the disjointness conjunct is satisfied by there being nothing seen yet.
-/
theorem distinctNames_iff (a : Array (String × α)) :
    distinctNames a = true ↔ (fieldNames a).Nodup := by
  rw [distinctNames, distinctNamesGo]
  simp

/--
Whether an object repeats a name depends on its names alone and not on the values beside them.
That is what lets the check survive any transformation that leaves the names where they are, which
is what a traversal of the values does.

`a` and `b` hold values of different types, `α` and `β`, so this is not an instance of
congruence within one type. `h : fieldNames a = fieldNames b` says the two agree as lists of
names, and the conclusion equates the two `Bool`s. It follows by rewriting both sides through
`distinctNames_iff`, `Nodup` being a property of the name list and of nothing else.
-/
theorem distinctNames_congr {a : Array (String × α)} {b : Array (String × β)}
    (h : fieldNames a = fieldNames b) : distinctNames a = distinctNames b := by
  rw [Bool.eq_iff_iff, distinctNames_iff, distinctNames_iff, h]

/--
Running a traversal over an object's values does not change whether its names repeat. `uniqueKeys`
both checks names at an object and descends into its values, so its recursive and folded forms can
only be proved equal if the check commutes with the traversal.

`a.runFields l` replaces each field's value by what the algebra makes of it, leaving the names
alone. The equation says the check gives the same answer on the result as on the input. It is
`distinctNames_congr` applied to `Alg.runFields_names`, which is where the names being untouched
is actually established.
-/
theorem distinctNames_runFields (a : Alg α) (l : List (String × Json)) :
    distinctNames (a.runFields l).toArray = distinctNames l.toArray :=
  distinctNames_congr (by simp [fieldNames, Alg.runFields_names])

mutual

/-- No object anywhere in the value has a repeated field name. -/
def uniqueKeys : Json → Bool
  | arr elems => uniqueKeysList elems.toList
  | obj fields => distinctNames fields && uniqueKeysFields fields.toList
  | _ => true

def uniqueKeysList : List Json → Bool
  | [] => true
  | j :: rest => uniqueKeys j && uniqueKeysList rest

def uniqueKeysFields : List (String × Json) → Bool
  | [] => true
  | (_, v) :: rest => uniqueKeys v && uniqueKeysFields rest

end

def uniqueKeysAlg : Alg Bool where
  null := true
  bool := fun _ => true
  num := fun _ => true
  str := fun _ => true
  arr := fun elems => elems.toList.foldr (· && ·) true
  obj := fun fields => distinctNames fields && fields.toList.foldr (fun p acc => p.2 && acc) true

mutual

/--
The check that no object anywhere repeats a name, written as a recursion, is the check the algebra
computes. `Json.RoundTrip` states a hypothesis in terms of `UniqueKeys` and the parser refuses a
duplicate name, so the recursion the proofs speak of has to be the traversal that runs.

`uniqueKeys` requires `distinctNames` at each object and descends into every member.
`uniqueKeysAlg` says the same at each node, with the conjunctions written as
`foldr (· && ·) true`, and `Alg.run` applies it by recursion. The object case needs
`distinctNames_runFields`, because the algebra checks the names of a field array whose values have
already been replaced by their answers.
-/
theorem uniqueKeys_eq_run : ∀ j : Json, uniqueKeys j = uniqueKeysAlg.run j
  | .null => rfl
  | .bool _ => rfl
  | .num _ => rfl
  | .str _ => rfl
  | .arr elems => by rw [uniqueKeys, Alg.run, uniqueKeysList_eq_run]; rfl
  | .obj fields => by
    rw [uniqueKeys, Alg.run, uniqueKeysFields_eq_run]
    simp only [uniqueKeysAlg, distinctNames_runFields, Array.toArray_toList]

/--
An array's elements are all free of repeated names exactly when the conjunction over them says so.
This is the array half of the mutual induction, and it is what fixes the empty array as `true`, so
a value holding no objects passes the check with nothing to examine.

`uniqueKeysList` conjoins as it recurses down the list; the right-hand side answers each element
separately, through `uniqueKeysAlg.runList`, and combines the answers with
`foldr (· && ·) true`. Both sides are `Bool` and both seed the empty list with `true`.
-/
theorem uniqueKeysList_eq_run : ∀ l : List Json,
    uniqueKeysList l = (uniqueKeysAlg.runList l).foldr (· && ·) true
  | [] => rfl
  | j :: rest => by
    rw [uniqueKeysList, Alg.runList, List.foldr_cons, uniqueKeys_eq_run j,
      uniqueKeysList_eq_run rest]

/--
An object's field values are all free of repeated names exactly when the conjunction over them
says so. Only what is nested inside the values is at issue here; the names of the object itself
are `distinctNames`' business at the node above.

`uniqueKeysFields` conjoins `uniqueKeys v` down the list, ignoring each name; the right-hand side
folds `p.2` over `uniqueKeysAlg.runFields l` from a seed of `true`. Both sides discard the names,
which is why this one, unlike the object case above, needs no claim about names surviving the
traversal.
-/
theorem uniqueKeysFields_eq_run : ∀ l : List (String × Json),
    uniqueKeysFields l = (uniqueKeysAlg.runFields l).foldr (fun p acc => p.2 && acc) true
  | [] => rfl
  | (k, v) :: rest => by
    rw [uniqueKeysFields, Alg.runFields, List.foldr_cons, uniqueKeys_eq_run v,
      uniqueKeysFields_eq_run rest]

end

def uniqueKeysFold (j : Json) : Bool := uniqueKeysAlg.fold j

/--
The compiler runs the stackless key check. The input on which the check matters most is a large,
deeply nested document from an untrusted source, which is exactly the input on which a recursion
would exhaust the C stack, so the two forms being one function is what makes running it safe.

`@uniqueKeys = @uniqueKeysFold` equates the functions over every value, which is what `@[csimp]`
requires before substituting one for the other in compiled code. `uniqueKeysFold` is
`uniqueKeysAlg.fold`; `Alg.fold_eq_run` reduces it to `uniqueKeysAlg.run` and `uniqueKeys_eq_run`
identifies that with `uniqueKeys`.
-/
@[csimp] theorem uniqueKeys_eq_uniqueKeysFold : @uniqueKeys = @uniqueKeysFold := by
  funext j
  rw [uniqueKeysFold, Alg.fold_eq_run, uniqueKeys_eq_run]

/-- `uniqueKeys` as a proposition, decidable by construction. -/
abbrev UniqueKeys (j : Json) : Prop := uniqueKeys j = true

mutual

/-- Every number in the value is in canonical form, which is what the parser guarantees. -/
def canonicalNumbers : Json → Bool
  | num n => decide n.Canonical
  | arr elems => canonicalNumbersList elems.toList
  | obj fields => canonicalNumbersFields fields.toList
  | _ => true

def canonicalNumbersList : List Json → Bool
  | [] => true
  | j :: rest => canonicalNumbers j && canonicalNumbersList rest

def canonicalNumbersFields : List (String × Json) → Bool
  | [] => true
  | (_, v) :: rest => canonicalNumbers v && canonicalNumbersFields rest

end

abbrev CanonicalNumbers (j : Json) : Prop := canonicalNumbers j = true

def canonicalNumbersAlg : Alg Bool where
  null := true
  bool := fun _ => true
  num := fun n => decide n.Canonical
  str := fun _ => true
  arr := fun elems => elems.toList.foldr (· && ·) true
  obj := fun fields => fields.toList.foldr (fun p acc => p.2 && acc) true

mutual

/--
The check that every number in a value is canonical, written as a recursion, is the check the
algebra computes. The printer's soundness carries this as a hypothesis, so a caller who built a
value rather than parsing one has to be able to run it, and what they run must be what was proved
about.

`canonicalNumbers` answers `decide n.Canonical` at a number, `true` at the other scalars, and
descends through arrays and objects; `canonicalNumbersAlg` says the same at each node and
`Alg.run` applies it by recursion. Nothing here inspects a field name, so unlike the key check it
needs no claim about names surviving the traversal.
-/
theorem canonicalNumbers_eq_run : ∀ j : Json, canonicalNumbers j = canonicalNumbersAlg.run j
  | .null => rfl
  | .bool _ => rfl
  | .num _ => rfl
  | .str _ => rfl
  | .arr elems => by rw [canonicalNumbers, Alg.run, canonicalNumbersList_eq_run]; rfl
  | .obj fields => by rw [canonicalNumbers, Alg.run, canonicalNumbersFields_eq_run]; rfl

/--
An array's elements all hold canonical numbers exactly when the conjunction over them says so.
Written out separately because the recursion and the algebra disagree in shape at a list, one
conjoining as it goes and the other combining answers already computed.

`canonicalNumbersList` conjoins as it recurses; the right-hand side answers each element through
`canonicalNumbersAlg.runList` and folds with `(· && ·)` from `true`. The empty list is `true` on
both sides, so an empty array is canonical by having nothing to check rather than by exception.
-/
theorem canonicalNumbersList_eq_run : ∀ l : List Json,
    canonicalNumbersList l = (canonicalNumbersAlg.runList l).foldr (· && ·) true
  | [] => rfl
  | j :: rest => by
    rw [canonicalNumbersList, Alg.runList, List.foldr_cons, canonicalNumbers_eq_run j,
      canonicalNumbersList_eq_run rest]

/--
An object's field values all hold canonical numbers exactly when the conjunction over them says
so. The names play no part: a name is a `String` and cannot hold a number, so nothing about it
could fail the check.

`canonicalNumbersFields` conjoins `canonicalNumbers v` down the list, discarding each name; the
right-hand side folds `p.2` over `canonicalNumbersAlg.runFields l` from a seed of `true`. Both
sides ignore the names, which is why the equation goes through without appeal to
`Alg.runFields_names`.
-/
theorem canonicalNumbersFields_eq_run : ∀ l : List (String × Json),
    canonicalNumbersFields l =
      (canonicalNumbersAlg.runFields l).foldr (fun p acc => p.2 && acc) true
  | [] => rfl
  | (k, v) :: rest => by
    rw [canonicalNumbersFields, Alg.runFields, List.foldr_cons, canonicalNumbers_eq_run v,
      canonicalNumbersFields_eq_run rest]

end

def canonicalNumbersFold (j : Json) : Bool := canonicalNumbersAlg.fold j

/--
The compiler runs the stackless canonicality check. It is a precondition of printing, so it may be
run on any value a caller has built, including one assembled programmatically to a great depth,
and it must not be the thing that crashes.

`@canonicalNumbers = @canonicalNumbersFold` equates the functions over every value, which is what
`@[csimp]` requires. `canonicalNumbersFold` is `canonicalNumbersAlg.fold`, which `Alg.fold_eq_run`
reduces to `canonicalNumbersAlg.run`, and `canonicalNumbers_eq_run` identifies that with
`canonicalNumbers`.
-/
@[csimp] theorem canonicalNumbers_eq_canonicalNumbersFold :
    @canonicalNumbers = @canonicalNumbersFold := by
  funext j
  rw [canonicalNumbersFold, Alg.fold_eq_run, canonicalNumbers_eq_run]

mutual

/--
How deeply the value nests: zero for a scalar, and one more than its deepest member for a
container. An empty container is one, entering it being what costs.
-/
def depth : Json → Nat
  | arr elems => depthList elems.toList + 1
  | obj fields => depthFields fields.toList + 1
  | _ => 0

def depthList : List Json → Nat
  | [] => 0
  | j :: rest => max (depth j) (depthList rest)

def depthFields : List (String × Json) → Nat
  | [] => 0
  | (_, v) :: rest => max (depth v) (depthFields rest)

end

def depthAlg : Alg Nat where
  null := 0
  bool := fun _ => 0
  num := fun _ => 0
  str := fun _ => 0
  arr := fun elems => elems.toList.foldr max 0 + 1
  obj := fun fields => fields.toList.foldr (fun p acc => max p.2 acc) 0 + 1

mutual

/--
Nesting depth written as a recursion is the depth the algebra computes. `maxDepth` is enforced
against this number and `Json.RoundTrip` states a hypothesis in terms of it, so what a caller
measures and what the parser refuses have to be one function.

`depth` gives a scalar zero and a container one more than its deepest member; `depthAlg` says the
same at each node and `Alg.run` applies it by recursion. The equation is between `Nat`s. An empty
container is one on both sides, entering it being what costs, so the two agree on the case where
the maximum has nothing to range over.
-/
theorem depth_eq_run : ∀ j : Json, depth j = depthAlg.run j
  | .null => rfl
  | .bool _ => rfl
  | .num _ => rfl
  | .str _ => rfl
  | .arr elems => by rw [depth, Alg.run, depthList_eq_run]; rfl
  | .obj fields => by rw [depth, Alg.run, depthFields_eq_run]; rfl

/--
The depth of an array's elements is the greatest of their depths, and zero when there are none.
The array case of `depth` goes through this, and it has to be stated in the algebra's shape, where
each element's answer is computed before the maximum is taken.

`depthList` takes `max` as it recurses; the right-hand side answers each element through
`depthAlg.runList` and folds with `max` from `0`. Zero is the seed on both sides, which is what
makes an empty array depth one rather than depth zero once the enclosing `+ 1` is added.
-/
theorem depthList_eq_run : ∀ l : List Json, depthList l = (depthAlg.runList l).foldr max 0
  | [] => rfl
  | j :: rest => by
    rw [depthList, Alg.runList, List.foldr_cons, depth_eq_run j, depthList_eq_run rest]

/--
The depth of an object's field values is the greatest of their depths, and zero when there are
none. Names contribute nothing to depth, however long they are, and this is where that is fixed.

`depthFields` takes `max` over the values as it recurses, discarding each name; the right-hand
side folds `max p.2` over `depthAlg.runFields l` from `0`. Both sides ignore the names, so the
equation needs nothing said about their surviving the traversal.
-/
theorem depthFields_eq_run : ∀ l : List (String × Json),
    depthFields l = (depthAlg.runFields l).foldr (fun p acc => max p.2 acc) 0
  | [] => rfl
  | (k, v) :: rest => by
    rw [depthFields, Alg.runFields, List.foldr_cons, depth_eq_run v, depthFields_eq_run rest]

end

def depthFold (j : Json) : Nat := depthAlg.fold j

/--
The compiler runs the stackless depth measure. Depth is what a caller computes in order to satisfy
the parser's nesting limit, so it is run on exactly the deep values that would overflow a
recursion, and measuring one must not be more dangerous than parsing it.

`@depth = @depthFold` equates the functions over every value, which is what `@[csimp]` requires
before it will substitute one for the other in compiled code. `depthFold` is `depthAlg.fold`,
which `Alg.fold_eq_run` reduces to `depthAlg.run`, and `depth_eq_run` identifies that with
`depth`.
-/
@[csimp] theorem depth_eq_depthFold : @depth = @depthFold := by
  funext j
  rw [depthFold, Alg.fold_eq_run, depth_eq_run]

/--
A value in a list is no deeper than the list. `depthList` is written as a fold of `max`, and this
is the half of being a maximum that the depth bounds actually use: that it dominates each member.

`j ∈ l` says `j` occurs somewhere in `l`, at any position. `depthList l` takes `max` down the
list from `0`, and `depth j ≤ depthList l` says that result is an upper bound for `j`. The
induction is on the membership proof, so the head and tail cases are separate; the empty list
raises no obligation, nothing being a member of it.
-/
theorem depth_le_depthList {j : Json} : ∀ {l : List Json}, j ∈ l → depth j ≤ depthList l
  | _ :: _, .head _ => by simp [depthList, Nat.le_max_left]
  | _ :: rest, .tail _ h => by
    have := depth_le_depthList (l := rest) h
    simp only [depthList]
    omega

/--
A value held by a field is no deeper than the object's fields taken together. Fields pair a name
with a value and only the value is measured, so this does not follow from the list case despite
being proved the same way.

`(k, v) ∈ l` says some field of `l` is named `k` and holds `v`. `depthFields l` takes `max` over
the values from `0`, and `depth v ≤ depthFields l` says that dominates `v`. The name `k` appears
in the hypothesis only to identify which field is meant; it is not measured on either side.
-/
theorem depth_le_depthFields {k : String} {v : Json} :
    ∀ {l : List (String × Json)}, (k, v) ∈ l → depth v ≤ depthFields l
  | _ :: _, .head _ => by simp [depthFields, Nat.le_max_left]
  | _ :: rest, .tail _ h => by
    have := depth_le_depthFields (l := rest) h
    simp only [depthFields]
    omega

/--
Every element of an array is strictly shallower than the array. This is what makes a recursion
spending one unit of depth per level terminate, and it is what turns a bound on a value's depth
into a bound on each of its members', which is how the parser's completeness proof carries a depth
limit downwards.

`h : j ∈ elems` says `j` is an element of the array. `depth (.arr elems)` is
`depthList elems.toList + 1`, and it is that `+ 1` that makes the inequality strict: an array is
one deeper than its deepest element, entering it being what costs. An empty array has no member,
so it raises no instance of the claim rather than a false one.
-/
theorem depth_arr_lt {j : Json} {elems : Array Json} (h : j ∈ elems) :
    depth j < depth (.arr elems) := by
  have hmem : j ∈ elems.toList := by simpa using h
  have := depth_le_depthList hmem
  simp only [depth]
  omega

/--
Every value held by an object is strictly shallower than the object. It is the object counterpart
of the array bound, needed separately because the two constructors hold differently shaped
contents, and used for the same purpose: descending into a value spends depth that is there to
spend.

`h : (k, v) ∈ fields` says the object has a field named `k` holding `v`. `depth (.obj fields)`
is `depthFields fields.toList + 1`, and the `+ 1` is what makes the inequality strict. The name is
not measured, so a long name buys no depth, and an object with no fields raises no instance.
-/
theorem depth_obj_lt {k : String} {v : Json} {fields : Array (String × Json)}
    (h : (k, v) ∈ fields) : depth v < depth (.obj fields) := by
  have hmem : (k, v) ∈ fields.toList := by simpa using h
  have := depth_le_depthFields hmem
  simp only [depth]
  omega

/-! ## Accessors

Each reads one thing and says in `Except String` why it could not, so that a wrong shape is a
value to handle rather than a panic. Where an object names a field twice, the last one wins.
-/

def getBool? : Json → Except String Bool
  | bool b => .ok b
  | _ => .error "expected a boolean"

def getNum? : Json → Except String Number
  | num n => .ok n
  | _ => .error "expected a number"

def getStr? : Json → Except String String
  | str s => .ok s
  | _ => .error "expected a string"

def getArr? : Json → Except String (Array Json)
  | arr elems => .ok elems
  | _ => .error "expected an array"

def getObj? : Json → Except String (Array (String × Json))
  | obj fields => .ok fields
  | _ => .error "expected an object"

def getInt? : Json → Except String Int
  | num n =>
    match n.toInt? with
    | some i => .ok i
    | none => .error "number is not an integer of a workable size"
  | _ => .error "expected a number"

def getNat? : Json → Except String Nat
  | num n =>
    match n.toNat? with
    | some i => .ok i
    | none => .error "number is not a natural number of a workable size"
  | _ => .error "expected a number"

def getObjVal? : Json → String → Except String Json
  | obj fields, k =>
    match findLast? fields k with
    | some v => .ok v
    | none => .error s!"no such field: {k}"
  | _, _ => .error "expected an object"

def getArrVal? : Json → Nat → Except String Json
  | arr elems, i =>
    match elems[i]? with
    | some v => .ok v
    | none => .error s!"index out of bounds: {i}"
  | _, _ => .error "expected an array"

def getObjValD (j : Json) (k : String) : Json :=
  (j.getObjVal? k).toOption.getD null

/-- Replaces the last field named `k`, or appends one, leaving other fields where they are. -/
def setObjVal? : Json → String → Json → Except String Json
  | obj fields, k, v =>
    match findLastIdx? fields k with
    | some i => .ok (obj (fields.setIfInBounds i (k, v)))
    | none => .ok (obj (fields.push (k, v)))
  | _, _, _ => .error "expected an object"

/-- `{...a, ...b}`, with `b`'s fields winning. Yields `b` when `a` is not an object. -/
def mergeObj : Json → Json → Json
  | obj a, obj b => obj (dedupKeys (a ++ b))
  | _, b => b

/-! ## Field arrays, one `push` at a time

`findLast?`, `findLastIdx?` and `dedupKeys` are each a left fold over the field array, so a claim
about any of them is a claim about what a fold accumulates, and `Array.pushInduction` is the
induction that fits: each fold has a single lemma saying what pushing a field does to it, and the
rest follows from those. `distinctNames` is a loop rather than a fold, and is read as `Nodup` of
the names where it is defined; what it gets here is a lemma of the same shape as the others.
-/

/--
Appending a field changes what lookup finds only for that field's own name, and for that name the
new value wins. `findLast?` is a left fold, so this single step is what `Array.pushInduction`
needs; almost everything else known about field lookup is derived from it.

`findLast? a k` is the value of the last field named `k`, or `none`. After `(key, v)` is pushed,
looking up `k` gives `v` when `key == k`, that field now being the last of its name, and otherwise
gives what it gave before. There is no case in which a push removes a binding, which is what makes
the `if` exhaustive.
-/
theorem findLast?_push (a : Array (String × α)) (key : String) (v : α) (k : String) :
    findLast? (a.push (key, v)) k = if key == k then some v else findLast? a k := by
  simp [findLast?]

/--
The counter that the position-finding fold carries is the number of fields it has passed. Nothing
can be said about the position `findLastIdx?` returns until the counter it is drawn from is known
to be the position the fold is at.

The fold accumulates a pair: the last matching position so far, and a running count. The claim
concerns only the second component, and says it ends at `a.size`. It holds for every `k`, since
the count is incremented once per field whether or not the name matched, which is exactly why the
first component can be read as a position.
-/
private theorem findLastIdxCount (a : Array (String × α)) (k : String) :
    (a.foldl (init := ((none : Option Nat), 0)) (fun (found, i) (key, _) =>
      (if key == k then some i else found, i + 1))).2 = a.size := by
  induction a using Array.pushInduction with
  | empty => rfl
  | push a x ih => rw [Array.foldl_push]; simpa using ih

/--
Appending a field puts it at the position one past the end, and leaves the position of every other
name where it was. With `findLast?_push` this is the pair of steps every induction over field
arrays takes.

`findLastIdx? a k` is the position of the last field named `k`. After `(key, v)` is pushed,
looking up `k` gives `a.size` when `key == k` and otherwise gives what it gave before. That the
new position is `a.size` rather than some other number is `findLastIdxCount`: the fold's counter
has reached the end of `a` by the time the new field arrives.
-/
theorem findLastIdx?_push (a : Array (String × α)) (key : String) (v : α) (k : String) :
    findLastIdx? (a.push (key, v)) k = if key == k then some a.size else findLastIdx? a k := by
  have h := findLastIdxCount a k
  simp only [findLastIdx?, Array.foldl_push] at *
  split <;> simp_all

/--
Lookup fails on exactly the names an object does not have. The accessors report a failed lookup as
an error, so without the direction that says a present name is found, a caller could not
distinguish a missing field from a broken lookup.

`fieldNames a` is the names in order. `findLast? a k = none ↔ k ∉ fieldNames a` reads both
ways: an absent name is not found, and a present name is. It says nothing about which value is
found, only that a field of that name exists somewhere in the array.
-/
theorem findLast?_eq_none_iff (a : Array (String × α)) (k : String) :
    findLast? a k = none ↔ k ∉ fieldNames a := by
  induction a using Array.pushInduction with
  | empty => simp [findLast?, fieldNames]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    by_cases h : key = k
    · subst h; simp [findLast?_push]
    · simp [findLast?_push, h, ih, Ne.symm h]

/--
A name has no position exactly when the object does not have it. Positions and values are found by
two separate folds, so their agreeing about which names exist is a claim in its own right, and it
is what lets an update be driven by the result of a lookup.

`findLastIdx? a k = none ↔ k ∉ fieldNames a` reads both ways: no position is reported for an
absent name, and one is reported for a present name. Which position that is belongs to
`findLastIdx?_eq_some`; here only the existence of one is at stake.
-/
theorem findLastIdx?_eq_none_iff (a : Array (String × α)) (k : String) :
    findLastIdx? a k = none ↔ k ∉ fieldNames a := by
  induction a using Array.pushInduction with
  | empty => simp [findLastIdx?, fieldNames]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    by_cases h : key = k
    · subst h; simp [findLastIdx?_push]
    · simp [findLastIdx?_push, h, ih, Ne.symm h]

/--
A position that lookup reports is a real position, holding a field of the name asked for, whose
value is the one the value lookup gives. This is what makes updating in place by index safe: the
index is in bounds, and it is the field the caller meant rather than some other.

`h` says the last field named `k` is at `i`. The conclusion bundles three facts. `hi : i < a.size`
puts `i` in bounds, so `a[i]` exists and a write there cannot be the silent no-op `setIfInBounds`
performs out of range. `a[i].1 = k` says that position holds the name asked for.
`findLast? a k = some a[i].2` says the two folds agree about the value as well as the position.
-/
theorem findLastIdx?_eq_some {a : Array (String × α)} {k : String} {i : Nat}
    (h : findLastIdx? a k = some i) :
    ∃ hi : i < a.size, a[i].1 = k ∧ findLast? a k = some a[i].2 := by
  induction a using Array.pushInduction with
  | empty => simp [findLastIdx?] at h
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    rw [findLastIdx?_push] at h
    by_cases hk : key = k
    · subst hk
      simp at h
      subst h
      refine ⟨by simp, ?_⟩
      simp [Array.getElem_push, findLast?_push]
    · simp [hk] at h
      obtain ⟨hi, hkey, hval⟩ := ih h
      refine ⟨by simp; omega, ?_⟩
      simp [Array.getElem_push, hi, findLast?_push, hk, hkey, hval]

/--
A position that lookup reports lies within the array. It is stated on its own because that is the
form an indexing or a `setIfInBounds` needs, without the rest of what is known about the position.

`h : findLastIdx? a k = some i` says `k`'s last field is at `i`, and the conclusion `i < a.size`
puts that index in bounds. It is the first component of `findLastIdx?_eq_some`, projected out.
-/
theorem findLastIdx?_lt {a : Array (String × α)} {k : String} {i : Nat}
    (h : findLastIdx? a k = some i) : i < a.size := (findLastIdx?_eq_some h).1

/--
A name that lookup finds has a position. This is what an in-place update needs: the caller learns
from `findLast?` that the field is there, and `setObjVal?` has to write it by index, so the two
lookups have to be known to succeed together.

`h : findLast? a k = some v` says a field named `k` exists and holds `v`. The conclusion says
`findLastIdx? a k` is a `some` as well, without saying which index, that being
`findLastIdx?_eq_some`'s business. It comes from the two `eq_none_iff` claims put together: both
folds fail on exactly the absent names, so neither can fail where the other succeeds.
-/
theorem findLastIdx?_isSome {a : Array (String × α)} {k : String} {v : α}
    (h : findLast? a k = some v) : ∃ i, findLastIdx? a k = some i := by
  cases hi : findLastIdx? a k with
  | some i => exact ⟨i, rfl⟩
  | none =>
    rw [(findLast?_eq_none_iff a k).2 ((findLastIdx?_eq_none_iff a k).1 hi)] at h
    exact absurd h (by simp)

/--
Replacing a field in place is exactly what lookup sees: the name written to yields the new value,
and no other name changes. Writing by index rather than rebuilding the array is what preserves
field order, and this is what says order is all that survives, nothing else having moved.

`h : findLastIdx? a k = some i` says `i` is where `k`'s last field is, so the write lands on that
field and not another; a write at an arbitrary index would not have this property. The equation is
over an arbitrary `k'`: looking that up in the updated array gives `v` when `k == k'` and
otherwise gives whatever `a` gave, so the name written and every other name are covered together.
-/
theorem findLast?_setIfInBounds {a : Array (String × α)} {k k' : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) :
    findLast? (a.setIfInBounds i (k, v)) k' = if k == k' then some v else findLast? a k' := by
  induction a using Array.pushInduction with
  | empty => simp [findLastIdx?] at h
  | push a x ih =>
    obtain ⟨key, w⟩ := x
    rw [findLastIdx?_push] at h
    by_cases hk : key = k
    · subst hk
      simp at h
      subst h
      rw [Array.setIfInBounds_push_size, findLast?_push, findLast?_push]
      by_cases hk' : key = k' <;> simp [hk']
    · simp [hk] at h
      rw [Array.setIfInBounds_push_lt (findLastIdx?_lt h), findLast?_push, findLast?_push, ih h]
      by_cases hk' : key = k' <;> by_cases hkk' : k = k' <;> simp_all

/--
Writing a field back where it already was, with the value already there, leaves the array
untouched. That is what lets `Json.set?` return the original document when the edit changes
nothing, field order and repeated names included, rather than a rebuilt one that merely looks up
the same.

`h` says the last field named `k` is at `i` and `hv` says its value is `v`, so `(k, v)` is
precisely `a[i]`. Under both, `a.setIfInBounds i (k, v) = a`. Neither hypothesis can be dropped:
without `h` the write could land on a different field, and without `hv` it could change the value
at the right one.
-/
theorem setIfInBounds_self {a : Array (String × α)} {k : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) (hv : findLast? a k = some v) :
    a.setIfInBounds i (k, v) = a := by
  obtain ⟨hi, hkey, hval⟩ := findLastIdx?_eq_some h
  rw [hv] at hval
  have hfield : (k, v) = a[i] := Prod.ext hkey.symm (Option.some.inj hval)
  rw [hfield, Array.setIfInBounds_getElem hi]


/--
Appending a field leaves the names distinct exactly when they already were and the new name is not
among them. This is the step that carries the check through `Array.pushInduction`, which is how
`dedupKeys` is proved to do what it claims.

`distinctNames (a.push x) = true` says the extended array repeats no name. The right-hand side
splits that in two: the array before the push repeats none, and `findLast? a x.1 = none`, which by
`findLast?_eq_none_iff` says the new name is absent. Stating the second half as a failed lookup
rather than as `∉ fieldNames a` is what makes it usable where a lookup has just been done.
-/
theorem distinctNames_push (a : Array (String × α)) (x : String × α) :
    distinctNames (a.push x) = true ↔ distinctNames a = true ∧ findLast? a x.1 = none := by
  rw [distinctNames_iff, distinctNames_iff, findLast?_eq_none_iff, fieldNames_push]
  simp only [List.nodup_append]
  grind

/--
Writing a new value to a field found by name leaves the names exactly as they were. Whether an
object repeats a name is a property of its names alone, so this is what carries `distinctNames`
across an in-place update.

`h : findLastIdx? a k = some i` says `i` is where `k`'s last field is, so the name being written,
`k`, is already the name at `i`. Without that the equation would be false rather than vacuous: a
write at an arbitrary index would replace one name with another. The conclusion equates the two
name lists, so both the names and their positions survive.
-/
theorem fieldNames_setIfInBounds {a : Array (String × α)} {k : String} {i : Nat} {v : α}
    (h : findLastIdx? a k = some i) : fieldNames (a.setIfInBounds i (k, v)) = fieldNames a := by
  obtain ⟨hi, hkey, _⟩ := findLastIdx?_eq_some h
  have hi' : i < (fieldNames a).length := by rw [fieldNames_length]; exact hi
  have hget : (fieldNames a)[i]'hi' = k := by simp [fieldNames, hkey]
  have hset : fieldNames (a.setIfInBounds i (k, v)) = (fieldNames a).set i k := by
    simp [fieldNames, Array.toList_setIfInBounds, List.map_set]
  rw [hset, ← hget, List.set_getElem_self]

/--
Deduplication appends a field whose name it has not kept before. `dedupKeys` is a fold whose step
branches on a lookup into what it has kept so far, and this is the branch taken when the name is
new.

`h : findLastIdx? (dedupKeys a) key = none` says the name is absent from the fields kept so far,
which by `findLastIdx?_eq_none_iff` is exactly when the fold takes this branch. The conclusion,
`dedupKeys (a.push (key, v)) = (dedupKeys a).push (key, v)`, puts the new field at the end, which
is what makes the surviving order the order of first appearance.
-/
theorem dedupKeys_push_none {a : Array (String × α)} {key : String} {v : α}
    (h : findLastIdx? (dedupKeys a) key = none) :
    dedupKeys (a.push (key, v)) = (dedupKeys a).push (key, v) := by
  simp only [dedupKeys, Array.foldl_push] at h ⊢
  rw [h]

/--
Deduplication overwrites, where it stands, a field whose name it has kept already. Keeping the
first position and the last value is the whole of what `dedupKeys` does, and this is the branch
that does it.

`h : findLastIdx? (dedupKeys a) key = some i` says the name has been kept, at position `i`. The
conclusion, `dedupKeys (a.push (key, v)) = (dedupKeys a).setIfInBounds i (key, v)`, replaces the
value at `i` and appends nothing, so the result does not grow and the name does not move. That `i`
is in bounds, and so that the write is not discarded, is `findLastIdx?_lt`.
-/
theorem dedupKeys_push_some {a : Array (String × α)} {key : String} {v : α} {i : Nat}
    (h : findLastIdx? (dedupKeys a) key = some i) :
    dedupKeys (a.push (key, v)) = (dedupKeys a).setIfInBounds i (key, v) := by
  simp only [dedupKeys, Array.foldl_push] at h ⊢
  rw [h]

/--
Deduplication leaves every lookup unchanged. That is what makes it safe to apply to an object
whose fields a caller may already have read: `mergeObj` produces a well-formed object without
changing the answer to any question that could have been asked of the fields it was given.

The equation `findLast? (dedupKeys a) k = findLast? a k` is for an arbitrary `k`, so it covers
names the array does not have as well as names it repeats. The induction is `Array.pushInduction`
over `a`, and its two cases are the fold's two branches, `dedupKeys_push_none` and
`dedupKeys_push_some`; the second appeals to `findLast?_setIfInBounds` to say the overwritten
value is the one lookup would have found anyway.
-/
theorem findLast?_dedupKeys (a : Array (String × α)) (k : String) :
    findLast? (dedupKeys a) k = findLast? a k := by
  induction a using Array.pushInduction with
  | empty => rfl
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    rw [findLast?_push]
    cases h : findLastIdx? (dedupKeys a) key with
    | none => rw [dedupKeys_push_none h, findLast?_push, ih]
    | some i => rw [dedupKeys_push_some h, findLast?_setIfInBounds h, ih]

/--
Deduplication really does deduplicate: what it returns repeats no name. Together with lookup being
unchanged, this is what `mergeObj` needs in order to build a well-formed object out of two that
may each repeat names.

`distinctNames (dedupKeys a) = true` says the result's names are pairwise distinct, for every `a`
whatsoever, with no hypothesis on the input. The induction is over pushes: the appending branch
uses `distinctNames_push`, whose second condition is exactly the lookup that put the fold in that
branch, and the overwriting branch uses `fieldNames_setIfInBounds`, the names being unchanged and
so still distinct.
-/
theorem distinctNames_dedupKeys (a : Array (String × α)) : distinctNames (dedupKeys a) = true := by
  induction a using Array.pushInduction with
  | empty => rw [distinctNames_iff]; simp [dedupKeys, fieldNames]
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    cases h : findLastIdx? (dedupKeys a) key with
    | none =>
      rw [dedupKeys_push_none h, distinctNames_push]
      exact ⟨ih, (findLast?_eq_none_iff _ _).2 ((findLastIdx?_eq_none_iff _ _).1 h)⟩
    | some i =>
      rw [dedupKeys_push_some h, distinctNames_iff, fieldNames_setIfInBounds h,
        ← distinctNames_iff]
      exact ih

/--
An object that repeats no name is returned untouched. Deduplication is therefore not a
normalisation that reorders or rebuilds: applied where there is nothing to do it does nothing, so
merging two well-formed objects yields their fields as they were written.

`distinctNames a = true` says the names are already pairwise distinct, and the conclusion is
equality of the arrays themselves, not merely agreement of what lookup finds. The induction is
over pushes: `distinctNames_push` turns distinctness of the extended array into distinctness of
the prefix together with absence of the new name, and that absence is what puts the fold in its
appending branch.
-/
theorem dedupKeys_eq_self :
    ∀ a : Array (String × α), distinctNames a = true → dedupKeys a = a := by
  intro a
  induction a using Array.pushInduction with
  | empty => intro _; rfl
  | push a x ih =>
    obtain ⟨key, v⟩ := x
    intro h
    rw [distinctNames_push] at h
    have hnone : findLastIdx? (dedupKeys a) key = none := by
      rw [ih h.1]
      exact (findLastIdx?_eq_none_iff a key).2 ((findLast?_eq_none_iff a key).1 h.2)
    rw [dedupKeys_push_none hnone, ih h.1]

/--
Deduplicating twice is deduplicating once. What `dedupKeys` produces is a fixed point of it, which
is what makes it a normal form rather than a step that could be repeated to further effect.

`dedupKeys (dedupKeys a) = dedupKeys a` is equality of arrays, so it says the second pass changes
nothing at all rather than nothing that lookup can see. It is `dedupKeys_eq_self` applied to
`distinctNames_dedupKeys`: the inner result repeats no name, and an array repeating no name is
left alone.
-/
theorem dedupKeys_dedupKeys (a : Array (String × α)) : dedupKeys (dedupKeys a) = dedupKeys a :=
  dedupKeys_eq_self _ (distinctNames_dedupKeys a)

end Json
