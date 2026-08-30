/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public section

namespace Json

@[expose] section

/-!
Numbers as JSON writes them, `mantissa * 10 ^ exponent`, with the exponent carried rather than
applied: `1e1000000000` is a pair of small integers here, where expanding it is a denial of
service.

`Canonical` picks one spelling of each value and the parser produces only canonical numbers, so
structural equality agrees with numeric equality on everything that came from text. `Ord`
compares numerically and so parts company with `=` on values that are not canonical; `Eqv` is
numeric equality as a proposition, and `eqv_iff_eq` ties the two together where it matters.

Every conversion out of a `Number` is bounded and says so in its type. `toInt?` and `toNat?`
refuse a number whose padding would run past `maxPadding` digits, which is what makes a
twelve-character text unable to ask for an integer of a billion digits.
-/

/-- A decimal number denoting `mantissa * 10 ^ exponent`. -/
structure Number where
  mantissa : Int
  exponent : Int
deriving DecidableEq, Hashable, Repr, Inhabited

namespace Number

/--
The mantissa of a number built from a mantissa and an exponent is the mantissa given. `Number` is
a structure and this is its first projection computing, stated so that `simp` can take a
constructed number apart without unfolding anything.

`(Number.mk m e).mantissa = m` holds by `rfl` for every pair of integers, `e` playing no part. It
is marked `@[simp]` because numbers are routinely built literally, in `Eqv` and in the grammar's
`Num` rule especially, and the projections then have to disappear on their own.
-/
@[simp] theorem mk_mantissa (m e : Int) : (Number.mk m e).mantissa = m := rfl

/--
The exponent of a number built from a mantissa and an exponent is the exponent given. The
companion to the mantissa projection, and needed as often, since almost every claim here
constrains the two components separately.

`(Number.mk m e).exponent = e` holds by `rfl` for every pair of integers, `m` playing no part. It
is `@[simp]` for the same reason as its companion: literal numbers appear throughout, and their
projections should not survive simplification.
-/
@[simp] theorem mk_exponent (m e : Int) : (Number.mk m e).exponent = e := rfl

/--
`n` is the unique representation of its value: either a mantissa with no trailing zero, or
zero paired with a zero exponent.

The exponent is never evaluated as a power of ten, so a number such as `1e1000000000` costs
nothing to represent.
-/
def Canonical (n : Number) : Prop :=
  n.mantissa % 10 ≠ 0 ∨ (n.mantissa = 0 ∧ n.exponent = 0)

instance : DecidablePred Canonical := fun n =>
  inferInstanceAs (Decidable (n.mantissa % 10 ≠ 0 ∨ (n.mantissa = 0 ∧ n.exponent = 0)))

/-- `n`'s mantissa rescaled to the exponent `k`, meaningful when `k ≤ n.exponent`. -/
def scaleTo (n : Number) (k : Int) : Int :=
  n.mantissa * 10 ^ (n.exponent - k).toNat

/--
`a` and `b` denote the same value, whatever their representations. Powers of ten appear here
only inside a proposition, where they are never computed.
-/
def Eqv (a b : Number) : Prop :=
  a.scaleTo (min a.exponent b.exponent) = b.scaleTo (min a.exponent b.exponent)

/--
A power of ten is positive. Comparison and rescaling multiply and divide by powers of ten
throughout, and every cancellation of one needs to know it is not zero and every inequality
multiplied through by one needs to know its sign.

`(0 : Int) < 10 ^ d` is over the integers, where the claim has content, `d` being a natural number
so that the power is never a reciprocal. It holds for `d = 0`, where the power is one, as well as
for every larger exponent.
-/
theorem pow_ten_pos (d : Nat) : (0 : Int) < 10 ^ d :=
  Int.pow_pos (by decide)

/--
A power of ten is not zero. This is the form the cancellation laws want: dividing an equation
through by a common power, which is how `Eqv` is shown to be symmetric and transitive, needs the
factor to be non-zero and nothing more.

`(10 : Int) ^ d ≠ 0` is the immediate consequence of `pow_ten_pos`, stated separately because
`Int.eq_of_mul_eq_mul_right` and its relatives ask for the inequality in this shape rather than
for positivity.
-/
theorem pow_ten_ne_zero (d : Nat) : (10 : Int) ^ d ≠ 0 :=
  Int.ne_of_gt (pow_ten_pos d)

/--
A number denotes the same value as itself. Numeric equivalence is defined by rescaling both sides
to a common exponent, so even reflexivity is a statement about that construction rather than
something to be assumed, and the rest of the equivalence is built on it.

`Eqv a a` unfolds to an equation whose two sides are the same term, `a` rescaled to
`min a.exponent a.exponent`, so it holds by `rfl` with no arithmetic at all.
-/
theorem Eqv.refl (a : Number) : Eqv a a := rfl

/--
Rescaling to a lower exponent multiplies by the power of ten between the two. Every comparison of
two numbers rescales them to a common exponent, and this is what says the choice of exponent does
not matter: going lower only introduces a common factor.

`n.scaleTo k` is `n`'s mantissa shifted so as to carry the exponent `k`, meaningful only when `k`
is at or below `n.exponent`, which `hk` and `hk'` together supply. The equation
`n.scaleTo k = n.scaleTo k' * 10 ^ (k' - k).toNat` factors the shift into a shift to the
intermediate `k'` and the remaining `k' - k`. `toNat` truncates a negative difference to zero,
which the two hypotheses are exactly what rule out.
-/
theorem scaleTo_lower {n : Number} {k k' : Int} (hk : k ≤ k') (hk' : k' ≤ n.exponent) :
    n.scaleTo k = n.scaleTo k' * 10 ^ (k' - k).toNat := by
  have hsplit : (n.exponent - k).toNat = (n.exponent - k').toNat + (k' - k).toNat := by omega
  simp only [scaleTo, hsplit, Int.pow_add, Int.mul_assoc]

/--
Two equivalent numbers rescale to the same integer at any exponent at or below both. Equivalence
is defined at one particular exponent, the minimum of the two, and this is what frees the rest of
the file to work at whatever exponent is convenient.

`hka` and `hkb` put `k` at or below both exponents, so neither rescaling truncates. Given
`h : Eqv a b`, which is that equality at the minimum, the conclusion `a.scaleTo k = b.scaleTo k`
is the same equality at `k`. It follows by factoring both sides through `scaleTo_lower` at the
minimum, where the common factor of `10 ^ (min - k)` appears on both.
-/
theorem scaleTo_eq_of_eqv {a b : Number} {k : Int} (hka : k ≤ a.exponent) (hkb : k ≤ b.exponent)
    (h : Eqv a b) : a.scaleTo k = b.scaleTo k := by
  rw [scaleTo_lower (n := a) (k := k) (k' := min a.exponent b.exponent) (by omega) (by omega),
    scaleTo_lower (n := b) (k := k) (k' := min a.exponent b.exponent) (by omega) (by omega), h]

/--
Agreement at any exponent at or below both is enough for equivalence. This is the converse
direction, and it is what lets a claim proved at a convenient exponent be recorded as `Eqv`.

`hka` and `hkb` put `k` at or below both exponents. From `h : a.scaleTo k = b.scaleTo k` the
conclusion `Eqv a b` follows by cancelling the common factor of
`10 ^ (min a.exponent b.exponent - k)` from both sides, legitimate because `pow_ten_ne_zero` says
it is not zero. Were the factor allowed to be zero the implication would fail, every pair agreeing
at a low enough `k`.
-/
theorem eqv_of_scaleTo {a b : Number} {k : Int} (hka : k ≤ a.exponent) (hkb : k ≤ b.exponent)
    (h : a.scaleTo k = b.scaleTo k) : Eqv a b := by
  refine Int.eq_of_mul_eq_mul_right (pow_ten_ne_zero (min a.exponent b.exponent - k).toNat) ?_
  rw [← scaleTo_lower (n := a) (by omega) (by omega),
    ← scaleTo_lower (n := b) (by omega) (by omega)]
  exact h

/--
Numeric equivalence is symmetric. It is defined as an equation at `min a.exponent b.exponent`, an
expression that is symmetric in the two numbers, but the surrounding `scaleTo` calls are not, so
symmetry has to be proved rather than read off.

`h : Eqv a b` gives the equation at the minimum exponent, and `Eqv b a` is the equation with the
sides exchanged. It goes through `scaleTo_eq_of_eqv` and `eqv_of_scaleTo` at that same minimum,
which is at or below both exponents, so both applications are within their hypotheses.
-/
theorem Eqv.symm {a b : Number} (h : Eqv a b) : Eqv b a :=
  eqv_of_scaleTo (k := min a.exponent b.exponent) (by omega) (by omega)
    (scaleTo_eq_of_eqv (by omega) (by omega) h).symm

/--
Numeric equivalence is transitive. With reflexivity and symmetry this makes it an equivalence
relation, which is what justifies reading it as "denote the same value" rather than as a relation
that merely happens to hold in particular cases.

`hab` and `hbc` are equations at two different minima, so neither can be chained onto the other as
it stands. The proof rescales all three to `min (min a.exponent b.exponent) c.exponent`, which is
at or below all of them, chains the equations there, and reads the result back as `Eqv a c`
through `eqv_of_scaleTo`.
-/
theorem Eqv.trans {a b c : Number} (hab : Eqv a b) (hbc : Eqv b c) : Eqv a c :=
  eqv_of_scaleTo (k := min (min a.exponent b.exponent) c.exponent) (by omega) (by omega)
    ((scaleTo_eq_of_eqv (by omega) (by omega) hab).trans
      (scaleTo_eq_of_eqv (by omega) (by omega) hbc))

/--
A number that survives multiplication by a power of ten with a non-zero last digit was multiplied
by ten to the zero. This is what turns "the mantissa has no trailing zero" into "the exponent
cannot have been shifted", which is the heart of canonical forms being unique.

`h : (m * 10 ^ d) % 10 ≠ 0` says the product's last decimal digit is not zero. The conclusion
`d = 0` says no shift took place. The case `d = d' + 1` is impossible because ten then divides the
product outright, whatever `m` is, so the hypothesis is what forces `d` down to zero.
-/
private theorem exponent_eq_zero_of_emod_ne {m : Int} {d : Nat}
    (h : (m * 10 ^ d) % 10 ≠ 0) : d = 0 := by
  match d with
  | 0 => rfl
  | d + 1 =>
    exact absurd (by rw [Int.pow_succ, ← Int.mul_assoc]; exact Int.mul_emod_left _ _) h

/--
Canonicity of a number built from a mantissa and an exponent is the condition on those two
components. `Canonical` is stated through the projections, so this is what lets it be checked
against a number written out literally, which is how the grammar and the parser both present one.

`Canonical ⟨m, e⟩ ↔ (m % 10 ≠ 0 ∨ (m = 0 ∧ e = 0))` reads the definition back: either
the mantissa has a non-zero last digit, so no factor of ten can be moved into the exponent, or the
number is exactly the zero written with a zero exponent. It holds by `Iff.rfl`, the projections
computing on a literal.
-/
@[simp] theorem canonical_mk {m e : Int} :
    Canonical ⟨m, e⟩ ↔ (m % 10 ≠ 0 ∨ (m = 0 ∧ e = 0)) := Iff.rfl

/--
Two canonical numbers whose mantissas differ by a power of ten are the same number. This is the
arithmetic core of canonical forms being unique, extracted from `Number` so that it can be stated
about four integers rather than about two structures.

`hle : ea ≤ eb` fixes which mantissa is the scaled one, and `h : ma = mb * 10 ^ (eb - ea).toNat`
says how. `ha` and `hb` are the canonicity conditions written out on the components. The
conclusion `ma = mb ∧ ea = eb` is that the two representations coincide. There are two cases: a
non-zero last digit in `ma` forces the power to be zero by `exponent_eq_zero_of_emod_ne`, and
`ma = 0` forces `mb = 0`, whereupon the second half of each canonicity condition pins both
exponents to zero.
-/
private theorem eq_of_scaled {ma mb ea eb : Int} (hle : ea ≤ eb)
    (ha : ma % 10 ≠ 0 ∨ (ma = 0 ∧ ea = 0)) (hb : mb % 10 ≠ 0 ∨ (mb = 0 ∧ eb = 0))
    (h : ma = mb * 10 ^ (eb - ea).toNat) : ma = mb ∧ ea = eb := by
  rcases ha with hma | ⟨hma, hea⟩
  · have hd : (eb - ea).toNat = 0 := exponent_eq_zero_of_emod_ne (h ▸ hma)
    rw [hd] at h
    exact ⟨by simpa using h, by omega⟩
  · subst hma
    have hmb : mb = 0 := by
      rcases Int.mul_eq_zero.mp h.symm with h' | h'
      · exact h'
      · exact absurd h' (Int.ne_of_gt (pow_ten_pos _))
    rcases hb with hmb' | ⟨_, heb⟩
    · exact absurd (by simp [hmb]) hmb'
    · exact ⟨hmb.symm, by omega⟩

/--
Two canonical numbers denote the same value exactly when they are the same term. This is why the
library may compare, order and hash parsed values structurally: `Json.Spec.Canonical` shows every
number in a parsed value is canonical, and here that turns structural equality into equality of
what the numbers mean.

`ha` and `hb` require both numbers to be canonical, and neither can be dropped: `⟨1, 0⟩` and
`⟨10, -1⟩` are equivalent and distinct, and the second is not canonical. Given both,
`Eqv a b`, the equation of rescaled mantissas, holds exactly when `a = b` as structures, mantissa
and exponent alike. The forward direction splits on which exponent is smaller and applies
`eq_of_scaled`; the reverse is immediate.
-/
theorem eqv_iff_eq {a b : Number} (ha : Canonical a) (hb : Canonical b) :
    Eqv a b ↔ a = b := by
  obtain ⟨ma, ea⟩ := a
  obtain ⟨mb, eb⟩ := b
  constructor
  · intro h
    simp only [Eqv, scaleTo] at h
    rcases Int.le_total ea eb with hle | hle
    · have h₁ : (ea - min ea eb).toNat = 0 := by omega
      have h₂ : (eb - min ea eb).toNat = (eb - ea).toNat := by omega
      rw [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := eq_of_scaled hle ha hb (by simpa using h)
      rfl
    · have h₁ : (eb - min ea eb).toNat = 0 := by omega
      have h₂ : (ea - min ea eb).toNat = (ea - eb).toNat := by omega
      rw [h₁, h₂] at h
      obtain ⟨rfl, rfl⟩ := eq_of_scaled hle hb ha (by simpa using h.symm)
      rfl
  · intro h
    injection h with hm he
    subst hm
    subst he
    rfl

def normalizeAux (m e : Int) : Number :=
  if h : m % 10 = 0 ∧ m ≠ 0 then normalizeAux (m / 10) (e + 1) else ⟨m, e⟩
termination_by m.natAbs
decreasing_by
  obtain ⟨h1, h2⟩ := h
  omega

/-- The canonical representation of `mantissa * 10 ^ exponent`. -/
def normalize (mantissa exponent : Int) : Number :=
  if mantissa = 0 then ⟨0, 0⟩ else normalizeAux mantissa exponent

/--
Stripping trailing zeros from a non-zero mantissa leaves a canonical number. This is the working
half of normalisation, the zero case being handled separately, and it is what makes `normalize` a
function into canonical forms rather than merely a tidying step.

`m ≠ 0` is required, and is what the claim genuinely needs: at `m = 0` the loop stops at once,
leaving `⟨0, e⟩`, which is canonical only when `e` is zero. Given it, the conclusion says the
result `normalizeAux m e` has a non-zero last digit. The induction follows the loop, which divides
by ten while the last digit is zero; the loop can only stop where that digit is not zero, which is
the first disjunct of `Canonical`.
-/
theorem canonical_normalizeAux : ∀ (m e : Int), m ≠ 0 → Canonical (normalizeAux m e) := by
  intro m e
  fun_induction normalizeAux m e with
  | case1 m e h ih =>
    intro _
    exact ih (by obtain ⟨h1, h2⟩ := h; omega)
  | case2 m e h =>
    intro hm
    exact Or.inl fun hc => h ⟨hc, hm⟩

/--
Normalisation always produces a canonical number. Every number the library manufactures goes
through it, from the grammar's `Num` rule to `ofInt` and `ofFloat?`, so this is what makes
canonicity an invariant rather than a property to be checked at each use.

`Canonical (normalize m e)` holds for every mantissa and exponent whatever, with no hypothesis.
`normalize` splits on `m = 0`, returning `⟨0, 0⟩`, which satisfies the second disjunct of
`Canonical`, and otherwise calling `normalizeAux`, whose result is canonical by the previous
claim. Between them the two cases leave nothing uncovered.
-/
theorem canonical_normalize (m e : Int) : Canonical (normalize m e) := by
  unfold normalize
  split
  next => exact Or.inr ⟨rfl, rfl⟩
  next hm => exact canonical_normalizeAux _ _ hm

/--
Dividing a mantissa by ten and raising the exponent by one leaves the value alone, when the last
digit is zero. This is the single step normalisation takes, so it is what makes normalisation
value-preserving rather than merely canonicalising.

`h : m % 10 = 0` says ten divides the mantissa exactly, so `m / 10` loses nothing. The conclusion
`Eqv ⟨m / 10, e + 1⟩ ⟨m, e⟩` says the two spellings denote one value. It is proved at
`k := e`, which is at or below both exponents, where the left rescales by exactly one factor of
ten and the right by none. Without `h` the division would truncate and the claim would be false.
-/
theorem eqv_div_ten {m e : Int} (h : m % 10 = 0) : Eqv ⟨m / 10, e + 1⟩ ⟨m, e⟩ := by
  refine eqv_of_scaleTo (k := e) (show (e : Int) ≤ e + 1 by omega) (Int.le_refl e) ?_
  have h1 : ((e + 1) - e).toNat = 1 := by omega
  have h2 : (e - e).toNat = 0 := by omega
  have hdm := Int.mul_ediv_add_emod m 10
  simp only [scaleTo, h1, h2, Int.pow_one, Int.pow_zero, Int.mul_one]
  omega

/--
Stripping trailing zeros does not change what a number denotes. Canonicity alone would be
satisfied by any function returning a fixed canonical number, so this is the half that says
normalisation is a choice of representative rather than a replacement.

`Eqv (normalizeAux m e) ⟨m, e⟩` says the loop's result and its input denote one value, for
every mantissa and exponent, the zero case included, where the loop stops immediately and
equivalence is reflexivity. The induction follows the loop, and each step is `eqv_div_ten`
composed with the equivalence already established, `Eqv.trans` being what allows the composition.
-/
private theorem eqv_normalizeAux (m e : Int) : Eqv (normalizeAux m e) ⟨m, e⟩ := by
  fun_induction normalizeAux m e with
  | case1 m e h ih => exact ih.trans (eqv_div_ten h.1)
  | case2 m e h => exact Eqv.refl _

/--
Normalisation does not change what a number denotes. Together with `canonical_normalize` this is
the whole specification of `normalize`: it returns a canonical number, and it returns one denoting
the value it was given.

`Eqv (normalize m e) ⟨m, e⟩` holds for every mantissa and exponent. The zero case is separate,
and is where the claim has some content: `normalize` discards the exponent entirely, returning
`⟨0, 0⟩`, and equivalence still holds because a zero mantissa rescales to zero at any
exponent. The non-zero case is `eqv_normalizeAux`.
-/
theorem eqv_normalize (m e : Int) : Eqv (normalize m e) ⟨m, e⟩ := by
  unfold normalize
  split
  next hm => subst hm; simp [Eqv, scaleTo]
  next => exact eqv_normalizeAux _ _

/--
Two numbers denote the same value exactly when they have the same normal form. This is what makes
numeric equivalence decidable, and the instance below is exactly this claim turned into a
computation.

`Eqv a b` is a statement about rescaled mantissas, with no immediate way to check it;
`normalize a.mantissa a.exponent = normalize b.mantissa b.exponent` is an equality of structures,
which `DecidableEq` settles. The forward direction chains `eqv_normalize` on each side around `h`
and appeals to `eqv_iff_eq`, both normal forms being canonical; the reverse chains them the other
way, needing no canonicity.
-/
theorem eqv_iff_normalize_eq {a b : Number} :
    Eqv a b ↔ normalize a.mantissa a.exponent = normalize b.mantissa b.exponent := by
  constructor
  · intro h
    refine (eqv_iff_eq (canonical_normalize _ _) (canonical_normalize _ _)).mp ?_
    exact ((eqv_normalize a.mantissa a.exponent).trans h).trans
      (eqv_normalize b.mantissa b.exponent).symm
  · intro h
    exact ((eqv_normalize a.mantissa a.exponent).symm.trans
      (h ▸ Eqv.refl _)).trans (eqv_normalize b.mantissa b.exponent)

instance (a b : Number) : Decidable (Eqv a b) :=
  decidable_of_iff _ eqv_iff_normalize_eq.symm

/--
A canonical number is its own normal form. Normalisation is therefore idempotent, and a value that
came from the parser can be passed through it without being rebuilt, which is what lets `cmp`
normalise both sides without penalising the ordinary case.

`h : Canonical n` is the hypothesis, and `normalize n.mantissa n.exponent = n` is an equality of
structures rather than an equivalence. It follows from `eqv_normalize`, which says the normal form
denotes the same value, and `eqv_iff_eq`, which upgrades that to equality because both the normal
form and `n` itself are canonical.
-/
theorem normalize_eq_self {n : Number} (h : Canonical n) :
    normalize n.mantissa n.exponent = n :=
  (eqv_iff_eq (canonical_normalize _ _) h).mp (eqv_normalize _ _)

/-- `mantissa * 10 ^ exponent` for an integer, in canonical form. -/
def ofInt (m : Int) : Number := normalize m 0

def ofNat (n : Nat) : Number := ofInt n

instance : OfNat Number n := ⟨ofNat n⟩

instance : Neg Number := ⟨fun n => ⟨-n.mantissa, n.exponent⟩⟩

/-- Multiply by a power of ten, which only ever adjusts the exponent. -/
def mulPow10 (n : Number) (k : Int) : Number :=
  if n.mantissa = 0 then n else ⟨n.mantissa, n.exponent + k⟩

instance : OfScientific Number where
  ofScientific m sign e := normalize m (if sign then -(e : Int) else (e : Int))

/--
An integer converted to a number is canonical. Values built in Lean rather than parsed go through
`ofInt` and `ofNat`, so this is what extends the parser's guarantee to values a caller assembles.

`Canonical (ofInt m)` holds for every integer, including zero, which normalises to `⟨0, 0⟩`.
`ofInt m` is `normalize m 0`, so this is `canonical_normalize` at a zero exponent; nothing about
`m` is used, trailing zeros in the integer being moved into the exponent by normalisation.
-/
theorem canonical_ofInt (m : Int) : Canonical (ofInt m) := canonical_normalize m 0

/--
Negation negates the mantissa. `Neg` is defined componentwise on the structure, and this is that
definition stated so that `simp` can see through it, which is what claims about the sign of a
number need.

`(-n).mantissa = -n.mantissa` holds by `rfl` for every number. It is `@[simp]` because the sign of
a number is read off its mantissa throughout the comparison, where a negated number would
otherwise have to be unfolded by hand.
-/
@[simp] theorem neg_mantissa (n : Number) : (-n).mantissa = -n.mantissa := rfl

/--
Negation leaves the exponent alone. This is the other half of negation being componentwise, and it
is what makes negation preserve canonicity: nothing moves between the two components.

`(-n).exponent = n.exponent` holds by `rfl` for every number. Marked `@[simp]` alongside its
companion, so that a negated number's components reduce without unfolding the instance.
-/
@[simp] theorem neg_exponent (n : Number) : (-n).exponent = n.exponent := rfl

/--
Negating a canonical number leaves it canonical. Numbers are negated when a text carries a minus
sign, so without this the parser would have to renormalise, and canonicity of a parsed value would
not follow from canonicity of its digits.

`h : Canonical n` gives one of the two disjuncts, and the conclusion gives the corresponding one
for `-n`. A non-zero last digit stays non-zero under negation, `-m % 10` being zero exactly when
`m % 10` is; and the zero case survives because negation touches neither the zero mantissa nor the
zero exponent.
-/
theorem canonical_neg {n : Number} (h : Canonical n) : Canonical (-n) := by
  rcases h with h | ⟨h₁, h₂⟩
  · exact Or.inl (by simp only [neg_mantissa]; omega)
  · exact Or.inr ⟨by simp [h₁], h₂⟩

/--
Multiplying by a power of ten leaves a canonical number canonical. The printer and the parser both
shift a number by adjusting its exponent, and this is what says such a shift does not have to be
followed by renormalisation.

`h : Canonical n` and any `k` whatever, positive or negative, give `Canonical (n.mulPow10 k)`.
`mulPow10` moves `k` into the exponent and leaves the mantissa alone, except that it returns a
zero number unchanged rather than giving it a non-zero exponent; that special case is what keeps
the claim true, since `⟨0, k⟩` is not canonical for `k` other than zero.
-/
theorem canonical_mulPow10 {n : Number} (h : Canonical n) (k : Int) :
    Canonical (n.mulPow10 k) := by
  unfold mulPow10
  split
  next => exact h
  next hm =>
    rcases h with h | ⟨h₁, _⟩
    · exact Or.inl h
    · exact absurd h₁ hm

/-- Decimal digits in `m`, counting `0` as one digit. -/
def digitCount (m : Int) : Nat :=
  go m.natAbs 1
where
  go (n acc : Nat) : Nat :=
    if n ≤ 9 then acc else go (n / 10) (acc + 1)
  termination_by n
  decreasing_by omega

/--
The digit-counting loop returns the position of the leading digit, and that position brackets the
number between consecutive powers of ten. The loop divides by ten until one digit is left, so what
it has counted can only be described by saying which power of ten the number lies between.

`1 ≤ n` excludes zero, which the loop would count as one digit without there being a power of
ten below it. The conclusion produces the `e` the loop will add to its accumulator, so that
`digitCount.go n acc = acc + e`, together with `10 ^ e ≤ n` and `n < 10 ^ (e + 1)`, which say
`e` is the count of digits after the first. The induction is on `n` by strong recursion, matching
the loop's division by ten.
-/
private theorem digitCountGo_bounds : ∀ (n acc : Nat), 1 ≤ n →
    ∃ e, digitCount.go n acc = acc + e ∧ 10 ^ e ≤ n ∧ n < 10 ^ (e + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro acc hn
    rw [digitCount.go]
    split
    next h => exact ⟨0, by simp, by simpa using hn, by simp; omega⟩
    next h =>
      obtain ⟨e, he, hle, hlt⟩ := ih (n / 10) (by omega) (acc + 1) (by omega)
      have hs : (10 : Nat) ^ (e + 1) = 10 ^ e * 10 := Nat.pow_succ ..
      have hs' : (10 : Nat) ^ (e + 1 + 1) = 10 ^ (e + 1) * 10 := Nat.pow_succ ..
      exact ⟨e + 1, by omega, by omega, by omega⟩
/--
Every integer has at least one digit. The comparison aligns two mantissas by their digit counts
and subtracts one from a count, so a count of zero would make that subtraction wrap and the
alignment wrong.

`1 ≤ digitCount m` holds for every integer, zero included, which is counted as one digit rather
than none. The zero case is separate, since `digitCountGo_bounds` excludes it; for a non-zero `m`
the bound is the loop's accumulator, which starts at one and only grows.
-/
theorem one_le_digitCount (m : Int) : 1 ≤ digitCount m := by
  rcases Nat.eq_zero_or_pos m.natAbs with h | h
  · simp [digitCount, h, digitCount.go]
  · obtain ⟨e, he, _, _⟩ := digitCountGo_bounds m.natAbs 1 h
    simp only [digitCount, he]
    omega

/--
An integer is smaller in magnitude than ten to its digit count. This is the upper half of what the
digit count means, and it is what lets the comparison decide two numbers by the positions of their
leading digits alone, without aligning their mantissas.

`m.natAbs < 10 ^ digitCount m` is about magnitude, the sign having been dealt with before the
comparison reaches this point. It holds for zero, whose count is one and whose magnitude is zero.
For a non-zero `m` it is the upper bracket from `digitCountGo_bounds`.
-/
theorem natAbs_lt_pow_digitCount (m : Int) : m.natAbs < 10 ^ digitCount m := by
  rcases Nat.eq_zero_or_pos m.natAbs with h | h
  · simp [digitCount, h, digitCount.go]
  · obtain ⟨e, he, _, hlt⟩ := digitCountGo_bounds m.natAbs 1 h
    simp only [digitCount, he]
    have : (1 : Nat) + e = e + 1 := by omega
    rw [this]
    exact hlt

/--
An integer is at least ten to one less than its digit count. This is the lower half of what the
digit count means, and with the upper half it is what makes the leading-digit position decisive:
two numbers whose positions differ cannot overlap.

`h : m ≠ 0` is needed, zero having a digit count of one but no power of ten beneath it. The
conclusion `10 ^ (digitCount m - 1) ≤ m.natAbs` uses truncated subtraction, which is safe
because `one_le_digitCount` puts the count at one or more. It is the lower bracket from
`digitCountGo_bounds`.
-/
theorem pow_digitCount_le {m : Int} (h : m ≠ 0) : 10 ^ (digitCount m - 1) ≤ m.natAbs := by
  have hpos : 0 < m.natAbs := Int.natAbs_pos.mpr h
  obtain ⟨e, he, hle, _⟩ := digitCountGo_bounds m.natAbs 1 hpos
  simp only [digitCount, he]
  have : 1 + e - 1 = e := by omega
  rw [this]
  exact hle

/--
Whether `a` denotes a smaller value than `b`. Only the sign, the position of the leading digit,
and mantissas aligned to a common digit count are ever computed, so the exponent's magnitude
never costs anything.
-/
def isLt (a b : Number) : Bool :=
  if a.mantissa < 0 && 0 ≤ b.mantissa then true
  else if 0 ≤ a.mantissa && b.mantissa < 0 then false
  else if a.mantissa = 0 then 0 < b.mantissa
  else if b.mantissa = 0 then a.mantissa < 0
  else
    let dA : Int := digitCount a.mantissa
    let dB : Int := digitCount b.mantissa
    let sA := dA + a.exponent
    let sB := dB + b.exponent
    if sA ≠ sB then
      if 0 < a.mantissa then sA < sB else sB < sA
    else if dA < dB then
      a.mantissa * 10 ^ (dB - dA).toNat < b.mantissa
    else
      a.mantissa < b.mantissa * 10 ^ (dA - dB).toNat

/--
Rescaling multiplies a magnitude by a power of ten. The comparison reasons about magnitudes and
signs separately, so the rescaling has to be pushed through `natAbs` before either can be
addressed.

`(n.scaleTo k).natAbs = n.mantissa.natAbs * 10 ^ (n.exponent - k).toNat` says the magnitude of the
rescaled mantissa is the magnitude of the mantissa times the shift. No hypothesis relates `k` to
the exponent: where `k` is above it, `toNat` truncates to zero on both sides alike.
-/
private theorem natAbs_scaleTo (n : Number) (k : Int) :
    (n.scaleTo k).natAbs = n.mantissa.natAbs * 10 ^ (n.exponent - k).toNat := by
  simp [scaleTo, Int.natAbs_mul, Int.natAbs_pow]
/--
Rescaling does not change whether a number is positive. Sign is what the comparison settles first,
and it has to settle it on the mantissa, which is available, rather than on the rescaled value,
which is what the claim is really about.

`0 < n.scaleTo k ↔ 0 < n.mantissa` reads both ways. It holds because the shift multiplied in is
a power of ten, positive by `pow_ten_pos`, so it preserves the sign in one direction and cancels
in the other. No relation between `k` and the exponent is needed.
-/
private theorem scaleTo_pos_iff (n : Number) (k : Int) : 0 < n.scaleTo k ↔ 0 < n.mantissa := by
  constructor
  · intro h
    exact Int.lt_of_mul_lt_mul_right (by simpa [scaleTo] using h) (Int.le_of_lt (pow_ten_pos _))
  · intro h
    exact Int.mul_pos h (pow_ten_pos _)

/--
Rescaling does not change whether a number is negative. The comparison's first two branches turn
on one number being negative and the other not, and both have to be read off mantissas.

`n.scaleTo k < 0 ↔ n.mantissa < 0` reads both ways, and holds for the same reason as its
positive counterpart: the power of ten multiplied in is strictly positive, so it neither
introduces nor removes a sign.
-/
private theorem scaleTo_neg_iff (n : Number) (k : Int) : n.scaleTo k < 0 ↔ n.mantissa < 0 := by
  constructor
  · intro h
    exact Int.lt_of_mul_lt_mul_right (by simpa [scaleTo] using h) (Int.le_of_lt (pow_ten_pos _))
  · intro h
    exact Int.mul_neg_of_neg_of_pos h (pow_ten_pos _)

/--
Rescaling does not change whether a number is zero. Zero is the case the comparison separates out
before aligning digit counts, `digitCount` having no useful lower bound at zero.

`n.scaleTo k = 0 ↔ n.mantissa = 0` reads both ways, and follows from a product being zero only
when a factor is, together with `pow_ten_ne_zero` ruling the power out as that factor.
-/
private theorem scaleTo_eq_zero_iff (n : Number) (k : Int) :
    n.scaleTo k = 0 ↔ n.mantissa = 0 := by
  simp [scaleTo, Int.mul_eq_zero, pow_ten_ne_zero]
/--
A rescaled mantissa is smaller in magnitude than ten to its digit count plus its shift. This is
the upper bracket from `digitCount` carried through a rescaling, which is the form the comparison
needs when it decides two numbers by leading-digit position.

`(n.scaleTo k).natAbs < 10 ^ (digitCount n.mantissa + (n.exponent - k).toNat)` splits the power
into the digit count and the shift. It is `natAbs_lt_pow_digitCount` multiplied through by the
shift, which is legitimate because that factor is strictly positive.
-/
private theorem scaleTo_lt_pow (n : Number) (k : Int) :
    (n.scaleTo k).natAbs < 10 ^ (digitCount n.mantissa + (n.exponent - k).toNat) := by
  rw [natAbs_scaleTo, Nat.pow_add]
  exact (Nat.mul_lt_mul_right (Nat.pow_pos (by omega))).mpr (natAbs_lt_pow_digitCount _)

/--
A rescaled mantissa is at least ten to one less than its digit count, plus its shift. The lower
bracket carried through a rescaling, and the counterpart of the upper one; together they place a
rescaled mantissa inside a range determined by its leading digit alone.

`h : n.mantissa ≠ 0` is inherited from `pow_digitCount_le`, which needs it for the same reason:
at zero there is no power of ten below the magnitude. The conclusion multiplies that lower bound
through by `10 ^ (n.exponent - k).toNat`, the shift.
-/
private theorem pow_le_scaleTo {n : Number} (h : n.mantissa ≠ 0) (k : Int) :
    10 ^ (digitCount n.mantissa - 1 + (n.exponent - k).toNat) ≤ (n.scaleTo k).natAbs := by
  rw [natAbs_scaleTo, Nat.pow_add]
  exact Nat.mul_le_mul_right _ (pow_digitCount_le h)

/--
A number whose leading digit sits lower is smaller in magnitude. This is what makes the comparison
fast: when the two numbers' leading digits are in different places, no mantissa need be aligned or
multiplied out, and the answer follows from two small integers.

`hb : b.mantissa ≠ 0` is what gives `b` a lower bracket at all. `h` compares the two
digit-count-plus-shift totals, which is where each leading digit falls once both are rescaled to
`k`. The conclusion is the strict inequality of magnitudes. It follows by putting `a` below
`10 ^ (its total)` and `b` at or above `10 ^ (its total - 1)`, which do not overlap once the
totals differ, `one_le_digitCount` being what keeps the subtraction honest.
-/
private theorem natAbs_scaleTo_lt {a b : Number} {k : Int} (hb : b.mantissa ≠ 0)
    (h : digitCount a.mantissa + (a.exponent - k).toNat
       < digitCount b.mantissa + (b.exponent - k).toNat) :
    (a.scaleTo k).natAbs < (b.scaleTo k).natAbs := by
  have h1 := scaleTo_lt_pow a k
  have h2 := pow_le_scaleTo hb k
  have hd : 1 ≤ digitCount b.mantissa := one_le_digitCount _
  have hmono : (10:Nat) ^ (digitCount a.mantissa + (a.exponent - k).toNat)
      ≤ 10 ^ (digitCount b.mantissa - 1 + (b.exponent - k).toNat) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/--
Rescaling does not change whether a number is non-negative. The comparison's sign branches are
written with `0 ≤`, so this is the form actually needed, and it is not the negation of either of
the other two on its own.

`0 ≤ n.scaleTo k ↔ 0 ≤ n.mantissa` reads both ways. It is assembled from the strict positive
case and the zero case, non-negativity being their disjunction on both sides of the equivalence.
-/
private theorem scaleTo_nonneg_iff (n : Number) (k : Int) :
    0 ≤ n.scaleTo k ↔ 0 ≤ n.mantissa := by
  have h1 := scaleTo_pos_iff n k
  have h2 := scaleTo_eq_zero_iff n k
  omega

/--
A rescaling can be cut at any point into two shifts. Aligning two mantissas to a common digit
count is exactly such a cut, and this is what lets the aligned comparison be recognised as the
rescaled one.

`h : (n.exponent - k).toNat = d + c` says how the shift is to be divided. The conclusion
`n.scaleTo k = (n.mantissa * 10 ^ d) * 10 ^ c` applies `d` to the mantissa and leaves `c` outside,
which is how the comparison brings one mantissa up to the other's digit count with a factor still
to spare.
-/
private theorem scaleTo_split {n : Number} {k : Int} {d c : Nat}
    (h : (n.exponent - k).toNat = d + c) :
    n.scaleTo k = (n.mantissa * 10 ^ d) * 10 ^ c := by
  simp only [scaleTo, h, Int.pow_add, Int.mul_assoc]

/--
Comparing after scaling the shorter mantissa up to the longer's digit count is comparing the two
numbers. This is one of the two branches taken when the leading digits fall in the same place, and
it is what says the comparison then needs a factor of ten no larger than the difference in digit
counts.

`hd` says `a`'s mantissa is the shorter and `hs` says the two leading digits fall in the same
place, so scaling `a` up by the difference brings the two into alignment. `hkb : k ≤ b.exponent`
is what makes `b`'s own shift a genuine one. The equivalence says the scaled comparison of
mantissas holds exactly when the rescaled comparison at `k` does; the common factor
`10 ^ (b.exponent - k)`, which `scaleTo_split` exposes, cancels because it is positive.
-/
private theorem aligned_left {a b : Number} {k : Int} (hkb : k ≤ b.exponent)
    (hd : digitCount a.mantissa < digitCount b.mantissa)
    (hs : (digitCount a.mantissa : Int) + a.exponent
        = (digitCount b.mantissa : Int) + b.exponent) :
    (a.mantissa * 10 ^ ((digitCount b.mantissa : Int) - (digitCount a.mantissa : Int)).toNat
        < b.mantissa) ↔ a.scaleTo k < b.scaleTo k := by
  have hA : a.scaleTo k =
      (a.mantissa * 10 ^ ((digitCount b.mantissa : Int) - (digitCount a.mantissa : Int)).toNat)
        * 10 ^ (b.exponent - k).toNat :=
    scaleTo_split (by omega)
  have hB : b.scaleTo k = b.mantissa * 10 ^ (b.exponent - k).toNat := by
    simp [scaleTo]
  rw [hA, hB]
  exact (Int.mul_lt_mul_right (pow_ten_pos _)).symm

/--
Comparing after scaling the shorter mantissa up, where the shorter is the second, is again
comparing the two numbers. It is the mirror of the other aligned branch and is needed separately
because the two mantissas play asymmetric roles in the comparison.

`hd` says `b`'s mantissa is no longer than `a`'s, which includes the case of equal counts, and
`hs` says the leading digits coincide. `hka : k ≤ a.exponent` makes `a`'s shift genuine. The
equivalence again cancels a common positive factor, this time `10 ^ (a.exponent - k)`, so the
comparison of scaled mantissas and the comparison of rescaled values stand or fall together.
-/
private theorem aligned_right {a b : Number} {k : Int} (hka : k ≤ a.exponent)
    (hd : digitCount b.mantissa ≤ digitCount a.mantissa)
    (hs : (digitCount a.mantissa : Int) + a.exponent
        = (digitCount b.mantissa : Int) + b.exponent) :
    (a.mantissa
        < b.mantissa * 10 ^ ((digitCount a.mantissa : Int) - (digitCount b.mantissa : Int)).toNat)
      ↔ a.scaleTo k < b.scaleTo k := by
  have hB : b.scaleTo k =
      (b.mantissa * 10 ^ ((digitCount a.mantissa : Int) - (digitCount b.mantissa : Int)).toNat)
        * 10 ^ (a.exponent - k).toNat :=
    scaleTo_split (by omega)
  have hA : a.scaleTo k = a.mantissa * 10 ^ (a.exponent - k).toNat := by
    simp [scaleTo]
  rw [hA, hB]
  exact (Int.mul_lt_mul_right (pow_ten_pos _)).symm

/--
The fast comparison agrees with the obvious one, which rescales both mantissas to a common
exponent and compares the integers. The obvious one cannot be run, since `1e1000000000` would
expand to a billion digits; this is what says the one that can be run gives the same answers.

`hka` and `hkb` put `k` at or below both exponents, so neither rescaling truncates; any such `k`
will do, a factor of ten shared by both sides leaving a comparison alone. The equivalence between
`isLt a b = true` and `a.scaleTo k < b.scaleTo k` covers every branch of the comparison: the sign
cases through `scaleTo_pos_iff` and its relatives, the differing-leading-digit case through
`natAbs_scaleTo_lt`, and the two aligned cases through `aligned_left` and `aligned_right`. Nothing
computes a power of ten larger than the difference in the two mantissas' digit counts.
-/
theorem isLt_iff {a b : Number} {k : Int} (hka : k ≤ a.exponent) (hkb : k ≤ b.exponent) :
    isLt a b = true ↔ a.scaleTo k < b.scaleTo k := by
  have hpa := scaleTo_pos_iff a k
  have hna := scaleTo_neg_iff a k
  have hza := scaleTo_eq_zero_iff a k
  have hqa := scaleTo_nonneg_iff a k
  have hpb := scaleTo_pos_iff b k
  have hnb := scaleTo_neg_iff b k
  have hzb := scaleTo_eq_zero_iff b k
  have hqb := scaleTo_nonneg_iff b k
  have hp : ((a.exponent - k).toNat : Int) = a.exponent - k := Int.toNat_of_nonneg (by omega)
  have hq : ((b.exponent - k).toNat : Int) = b.exponent - k := Int.toNat_of_nonneg (by omega)
  unfold isLt
  split
  next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [true_iff]
    omega
  split
  next h =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine iff_of_false (by simp) ?_
    omega
  split
  next h =>
    simp only [decide_eq_true_eq]
    omega
  split
  next h =>
    simp only [decide_eq_true_eq]
    omega
  rename_i h₁ h₂ ha0 hb0
  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h₁ h₂
  split
  next hposa =>
    have hposb : 0 < b.mantissa := by omega
    have hAv : ((a.scaleTo k).natAbs : Int) = a.scaleTo k := Int.natAbs_of_nonneg (by omega)
    have hBv : ((b.scaleTo k).natAbs : Int) = b.scaleTo k := Int.natAbs_of_nonneg (by omega)
    simp only []
    split
    next hne =>
      simp only [decide_eq_true_eq]
      rcases Int.lt_trichotomy (digitCount a.mantissa + a.exponent : Int)
          (digitCount b.mantissa + b.exponent : Int) with hs | hs | hs
      · have := natAbs_scaleTo_lt (a := a) (b := b) (k := k) hb0 (by omega)
        exact iff_of_true hs (by omega)
      · exact absurd hs hne
      · have := natAbs_scaleTo_lt (a := b) (b := a) (k := k) ha0 (by omega)
        exact iff_of_false (by omega) (by omega)
    next hne =>
      split
      next hd =>
        simpa only [decide_eq_true_eq] using
          aligned_left (a := a) (b := b) hkb (by omega) (by omega)
      next hd =>
        simpa only [decide_eq_true_eq] using
          aligned_right (a := a) (b := b) hka (by omega) (by omega)
  next hposa =>
    have hnega : a.mantissa < 0 := by omega
    have hnegb : b.mantissa < 0 := by omega
    have hAv : ((a.scaleTo k).natAbs : Int) = -a.scaleTo k :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    have hBv : ((b.scaleTo k).natAbs : Int) = -b.scaleTo k :=
      Int.ofNat_natAbs_of_nonpos (by omega)
    simp only []
    split
    next hne =>
      simp only [decide_eq_true_eq]
      rcases Int.lt_trichotomy (digitCount a.mantissa + a.exponent : Int)
          (digitCount b.mantissa + b.exponent : Int) with hs | hs | hs
      · have := natAbs_scaleTo_lt (a := a) (b := b) (k := k) hb0 (by omega)
        exact iff_of_false (by omega) (by omega)
      · exact absurd hs hne
      · have := natAbs_scaleTo_lt (a := b) (b := a) (k := k) ha0 (by omega)
        exact iff_of_true (by omega) (by omega)
    next hne =>
      split
      next hd =>
        simpa only [decide_eq_true_eq] using
          aligned_left (a := a) (b := b) hkb (by omega) (by omega)
      next hd =>
        simpa only [decide_eq_true_eq] using
          aligned_right (a := a) (b := b) hka (by omega) (by omega)

/--
The equality case is decided by canonical form, so it is exact; the remaining branch only has to
choose between `lt` and `gt`, and can never report `eq`.
-/
def cmp (a b : Number) : Ordering :=
  if normalize a.mantissa a.exponent = normalize b.mantissa b.exponent then .eq
  else if isLt a b then .lt else .gt

instance : Ord Number := ⟨cmp⟩

/--
The comparison reports equality exactly on numbers that denote the same value, whatever their
spellings. `Ord` is expected to report `eq` on values that compare equal, and here that has to
mean numeric equality rather than equality of representations, since a non-canonical number is
representable.

`cmp a b = .eq ↔ Eqv a b` reads both ways. `cmp` decides its equality branch by comparing normal
forms, which `eqv_iff_normalize_eq` says is equivalence exactly; the remaining branch chooses
between `.lt` and `.gt` and so can never report `.eq`, which is what makes the reverse direction
hold rather than merely the forward one.
-/
theorem cmp_eq_eq_iff_eqv {a b : Number} : cmp a b = .eq ↔ Eqv a b := by
  unfold cmp
  split
  next h => exact iff_of_true rfl (eqv_iff_normalize_eq.mpr h)
  next h =>
    refine iff_of_false ?_ (fun he => h (eqv_iff_normalize_eq.mp he))
    split <;> simp

/--
On canonical numbers the comparison reports equality exactly on numbers that are the same term.
This is the form a caller uses: everything parsed is canonical, so `compare` and `==` agree, and
sorting a parsed document does not reorder values it considers equal.

`ha` and `hb` require both to be canonical, and without them the claim is false, `⟨1, 0⟩` and
`⟨10, -1⟩` comparing equal while differing as terms. Given them, `cmp a b = .eq ↔ a = b`. It
is `cmp_eq_eq_iff_eqv` composed with `eqv_iff_eq`, which is where canonicity is used.
-/
theorem cmp_eq_eq_iff_eq {a b : Number} (ha : Canonical a) (hb : Canonical b) :
    cmp a b = .eq ↔ a = b :=
  cmp_eq_eq_iff_eqv.trans (eqv_iff_eq ha hb)

/--
The whole comparison, not merely its equality case, agrees with rescaling both numbers to a common
exponent and comparing the integers. That is the specification `Ord Number` is judged against, and
it is what says the ordering is the numeric one rather than an artefact of representation.

`hka` and `hkb` put `k` at or below both exponents; any such `k` gives the same answer.
`cmp a b = compare (a.scaleTo k) (b.scaleTo k)` is an equality of `Ordering`s, so all three
outcomes are covered. The `.eq` case comes from `eqv_iff_normalize_eq` with `scaleTo_eq_of_eqv`;
the other two from `isLt_iff`, with `eqv_of_scaleTo` supplying the fact that the rescaled integers
differ whenever the normal forms do.
-/
theorem cmp_eq_compare_scaleTo {a b : Number} {k : Int} (hka : k ≤ a.exponent)
    (hkb : k ≤ b.exponent) : cmp a b = compare (a.scaleTo k) (b.scaleTo k) := by
  unfold cmp
  split
  next h =>
    have heq : a.scaleTo k = b.scaleTo k :=
      scaleTo_eq_of_eqv hka hkb (eqv_iff_normalize_eq.mpr h)
    simp [heq]
  next h =>
    have hne : a.scaleTo k ≠ b.scaleTo k := fun he =>
      h (eqv_iff_normalize_eq.mp (eqv_of_scaleTo hka hkb he))
    split
    next hlt => exact (Int.compare_eq_lt.mpr ((isLt_iff hka hkb).mp hlt)).symm
    next hlt =>
      have hge : ¬ a.scaleTo k < b.scaleTo k := fun hc => hlt ((isLt_iff hka hkb).mpr hc)
      exact (Int.compare_eq_gt.mpr (by omega)).symm



/--
The integer `n` denotes, when it denotes one and writing it out costs at most `maxPadding`
zeros beyond the digits already present in the mantissa.

The bound is on the padding rather than on the result, because the cost that has to be
refused is the one a short text can inflict: `1e1000000000` is twelve characters and an
integer of a billion digits. A mantissa that is itself long has already been paid for by
whoever holds it, so it passes.
-/
def toInt? (n : Number) (maxPadding : Nat := 1000) : Option Int :=
  if n.mantissa = 0 then
    some 0
  else if 0 ≤ n.exponent then
    if n.exponent ≤ (maxPadding : Int) then
      some (n.mantissa * 10 ^ n.exponent.toNat)
    else
      none
  else
    -- Below one in magnitude unless the mantissa's own trailing zeros absorb the exponent, so
    -- the power of ten computed here is bounded by the mantissa's length.
    let k := (-n.exponent).toNat
    if k ≤ digitCount n.mantissa then
      let p : Int := 10 ^ k
      if n.mantissa % p = 0 then some (n.mantissa / p) else none
    else
      none

/-- As `toInt?`, refusing a negative value as well as an over-padded one. -/
def toNat? (n : Number) (maxPadding : Nat := 1000) : Option Nat :=
  match n.toInt? maxPadding with
  | some i => if 0 ≤ i then some i.toNat else none
  | none => none

/--
The nearest `Float`, saturating to zero or an infinity outside the double range and truncating
mantissas far longer than a double can represent. Not verified against IEEE 754.
-/
def toFloat (n : Number) : Float :=
  if n.mantissa = 0 then
    0.0
  else
    let sign : Float := if n.mantissa < 0 then -1.0 else 1.0
    let d := digitCount n.mantissa
    let (m, e) :=
      if d ≤ 40 then (n.mantissa.natAbs, n.exponent)
      else (n.mantissa.natAbs / 10 ^ (d - 40), n.exponent + ((d - 40 : Nat) : Int))
    if e < -400 then sign * 0.0
    else if 400 < e then sign * (1.0 / 0.0)
    else if e < 0 then sign * OfScientific.ofScientific m true (-e).toNat
    else sign * OfScientific.ofScientific m false e.toNat

/--
The exact value of `x`, or `none` for a NaN or an infinity, neither of which JSON can express.

A `Float` is `m * 2 ^ e` for integers `m` and `e`, and every such value has a finite decimal
expansion, because `2 ^ e = 5 ^ -e * 10 ^ e` when `e` is negative. So the conversion is exact,
at the cost of being long: fifty significant digits is ordinary and a subnormal reaches several
hundred. The alternative, converting through the shortest decimal spelling a `Float` prints,
loses the value outright for small magnitudes.
-/
def ofFloat? (x : Float) : Option Number :=
  let bits := x.toBits.toNat
  let frac := bits % 0x10000000000000
  let biased := bits / 0x10000000000000 % 0x800
  -- A subnormal has no implicit leading bit, and takes the exponent of the smallest normal.
  let m : Nat := if biased = 0 then frac else frac + 0x10000000000000
  let e : Int := if biased = 0 then -1074 else (biased : Int) - 1075
  let signed : Int := if 0x8000000000000000 ≤ bits then -(m : Int) else (m : Int)
  if biased = 0x7FF then none
  else if 0 ≤ e then some (normalize (signed * 2 ^ e.toNat) 0)
  else some (normalize (signed * 5 ^ (-e).toNat) e)

/--
A number converted from a `Float` is canonical. Values reach the library from Lean floats as well
as from text, and canonicity is what everything downstream assumes, so the conversion has to
establish it rather than leave it to the caller.

`h : ofFloat? x = some n` is the successful case; a NaN or an infinity yields `none` and raises no
obligation, JSON being unable to express either. Every branch that does return a number builds it
with `normalize`, so `Canonical n` is `canonical_normalize` in each case, whether the exponent was
handled by multiplying out a power of two or by a power of five.
-/
theorem canonical_ofFloat {x : Float} {n : Number} (h : ofFloat? x = some n) : Canonical n := by
  simp only [ofFloat?] at h
  repeat' split at h
  all_goals first
    | (injection h with h; exact h ▸ canonical_normalize _ _)
    | simp at h


/--
Normalisation only ever moves the exponent up, one trailing zero at a time. That is what bounds
the padding `toInt?` has to write out: a normalised integer's exponent is at most the number of
trailing zeros it had, so an integer round trip cannot demand more digits than it started with.

`e ≤ (normalizeAux m e).exponent` holds for every mantissa and exponent, the loop either
stopping at once, where the two are equal, or dividing the mantissa by ten and adding one to the
exponent. The induction follows the loop, and each step only increases the exponent, so nothing is
claimed about how far it rises.
-/
theorem le_exponent_normalizeAux (m e : Int) : e ≤ (normalizeAux m e).exponent := by
  fun_induction normalizeAux m e with
  | case1 m e h ih => omega
  | case2 m e h => simp

/--
An integer written into a number and read back out is the integer it was. Together with the
canonicity of `ofInt` this is what makes the integer accessors a faithful round trip rather than
an approximation, which matters because `getInt?` is how most callers take a number out.

`h : (ofInt i).exponent ≤ (maxPadding : Int)` is the hypothesis that reading back stays within
the padding bound, and it is not vacuous: `le_exponent_normalizeAux` puts that exponent at the
count of `i`'s trailing zeros, so the bound is met by any integer with at most `maxPadding` of
them, which at the default of one thousand is every integer a caller is likely to hold. The
conclusion `(ofInt i).toInt? maxPadding = some i` says the read succeeds and returns `i` itself,
so neither the normalisation nor the padding has lost anything.
-/
theorem toInt?_ofInt {i : Int} {maxPadding : Nat}
    (h : (ofInt i).exponent ≤ (maxPadding : Int)) :
    (ofInt i).toInt? maxPadding = some i := by
  have hexp : 0 ≤ (normalize i 0).exponent := by
    unfold normalize
    split
    · simp
    · exact le_exponent_normalizeAux i 0
  have hval : (normalize i 0).mantissa * 10 ^ (normalize i 0).exponent.toNat = i := by
    have heqv := eqv_normalize i 0
    simp only [Eqv, scaleTo, show min (normalize i 0).exponent 0 = 0 by omega] at heqv
    simpa using heqv
  have h' : (normalize i 0).exponent ≤ (maxPadding : Int) := h
  by_cases hm : (normalize i 0).mantissa = 0
  · have hi : i = 0 := by simpa [hm] using hval.symm
    simp [ofInt, toInt?, normalize, hi]
  · simp [ofInt, toInt?, hm, hexp, h', hval]

/--
A natural number written into a number and read back out is the natural number it was. `toNat?`
adds a sign check to `toInt?`, and this says that check does not reject a value that was
non-negative to begin with.

`h : (ofNat n).exponent ≤ (maxPadding : Int)` is again the padding bound, met for the same
reason as in the integer case. The conclusion `(ofNat n).toNat? maxPadding = some n` says the read
succeeds and returns `n`. It is `toInt?_ofInt` at the integer `n`, whose result is non-negative
and so survives the extra check.
-/
theorem toNat?_ofNat {n : Nat} {maxPadding : Nat}
    (h : (ofNat n).exponent ≤ (maxPadding : Int)) :
    (ofNat n).toNat? maxPadding = some n := by
  simp [toNat?, ofNat, toInt?_ofInt h]

end Number

end

end Json
