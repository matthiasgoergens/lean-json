/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec

public section

namespace Json.Spec

/-!
What a production can begin with, and what may follow one.

The relations are deliberately not deterministic in their remainder, exactly as the ABNF is not:
`12` derives as `1` with `2` left over as readily as it derives as `12`, and a run of whitespace
can be divided anywhere. Both proofs about the grammar need the same conditions to pin that down,
and both need to know which character each production starts with, so those live here rather than
in either of them.
-/

/-- A list that whitespace cannot be taken from, which is where a `Ws` derivation has to stop. -/
@[expose] def NoWs (l : List Char) : Prop := ∀ c t, l = c :: t → isWs c = false

/-- What may follow a value: the end of the text, whitespace, or a separator or closing bracket. -/
@[expose] def Follows (l : List Char) : Prop :=
  ∀ c t, l = c :: t → isWs c = true ∨ c = ',' ∨ c = ']' ∨ c = '}'

/--
Two runs of whitespace taken one after the other are a single run. Every structural character in
the grammar carries whitespace on both sides, so a proof routinely holds two adjacent runs and has
to see them as one.

`h₁ : Ws a b` and the second argument `Ws b c` say whitespace took `a` to `b` and then `b` to
`c`; `Ws a c` says one run takes `a` to `c`. The induction is on `h₁`, rebuilding each `cons`
around the second run. Nothing is said about where the join fell, which is what makes the result
usable however the two runs were obtained.
-/
theorem Ws.trans {a b c : List Char} (h₁ : Ws a b) : Ws b c → Ws a c := by
  induction h₁ with
  | nil => exact fun h => h
  | cons hc _ ih => exact fun h => Ws.cons hc (ih h)

/--
Two runs of whitespace taken from the same text agree as far as the shorter of them goes. The
grammar lets a run stop anywhere, so without this two derivations of one text could part company
at the first space and never be compared again.

`h₁ : Ws s r₁` and the second run `Ws s r₂` both start at `s`. The conclusion
`Ws r₁ r₂ ∨ Ws r₂ r₁` says one remainder is reachable from the other by whitespace,
without saying which, so it is a statement that the two are comparable rather than that either is
further on. The induction is on `h₁`; where the first run consumed nothing, the second is itself
the witness.
-/
theorem Ws.confluent {s r₁ : List Char} (h₁ : Ws s r₁) :
    ∀ {r₂ : List Char}, Ws s r₂ → Ws r₁ r₂ ∨ Ws r₂ r₁ := by
  induction h₁ with
  | nil => exact fun h₂ => Or.inl h₂
  | @cons c s r hc h₁' ih =>
    intro r₂ h₂
    cases h₂ with
    | nil => exact Or.inr (Ws.cons hc h₁')
    | cons _ h₂' => exact ih h₂'

/--
Whitespace stops in exactly one place, once what follows it is required not to be whitespace. This
is what turns the grammar's freedom about where a run ends into a determinate answer, and it is
the form the parser's completeness proof needs in order to say the parser and the grammar stopped
at the same character.

`h₁` and `h₂` are two runs from the same `s`, and `n₁` and `n₂` say neither remainder
begins with a whitespace character. The conclusion `r₁ = r₂` is equality of those remainders.
`Ws.confluent` gives a run between them in one direction or the other, and that run can only be
empty: a `cons` step would need a leading whitespace character, which `NoWs` denies.
-/
theorem Ws.eq_of_noWs {s r₁ r₂ : List Char} (h₁ : Ws s r₁) (h₂ : Ws s r₂)
    (n₁ : NoWs r₁) (n₂ : NoWs r₂) : r₁ = r₂ := by
  rcases h₁.confluent h₂ with h | h
  · cases h with
    | nil => rfl
    | cons hc _ => rw [n₁ _ _ rfl] at hc; exact absurd hc (by decide)
  · cases h with
    | nil => rfl
    | cons hc _ => rw [n₂ _ _ rfl] at hc; exact absurd hc (by decide)

/--
No whitespace can be taken from a text that begins with none. This is the degenerate case of a
run, and having it lets a proof pass over an absent run rather than case-split on it every time.

`h : Ws l x` is a run from `l` and `hn : NoWs l` says `l` does not begin with a whitespace
character. The conclusion `l = x` says the run consumed nothing. `Ws.cons` is what has to be
excluded, and `hn` applied to `l`'s own head is exactly what excludes it.
-/
theorem Ws.source_eq_of_noWs {l x : List Char} (h : Ws l x) (hn : NoWs l) : l = x := by
  cases h with
  | nil => rfl
  | cons hc _ => rw [hn _ _ rfl] at hc; exact absurd hc (by decide)

/--
Of two runs of whitespace from one text, the one whose remainder holds no more whitespace is at
least as far on. This is the directed form of confluence, and it is what says a parser that skips
whitespace greedily has gone no less far than any derivation.

`h₁ : Ws x y` and `h₂ : Ws x z` are two runs from `x`, and `hn : NoWs z` says the second
stopped where nothing more can be taken. The conclusion `Ws y z` places `z` at or beyond `y`.
Confluence supplies one direction outright; in the other, `Ws.source_eq_of_noWs` collapses the run
from `z` to `y`, which makes the two remainders equal and the conclusion `Ws.nil`.
-/
theorem Ws.to_noWs {x y z : List Char} (h₁ : Ws x y) (h₂ : Ws x z) (hn : NoWs z) : Ws y z := by
  rcases h₁.confluent h₂ with h | h
  · exact h
  · rw [← h.source_eq_of_noWs hn]
    exact Ws.nil

/--
A text whose first character is not whitespace begins with none. `NoWs` is phrased as a condition
on however the list may be split into a head and a tail, and this is how it is discharged wherever
that head is already known.

`h : isWs t = false` says the leading character is not whitespace. `NoWs (t :: u)` quantifies over
every way of writing the list as a head and a tail, of which a `cons` admits exactly one, so
discharging it amounts to producing `h` again. The tail `u` is unconstrained.
-/
theorem noWs_cons {t : Char} {u : List Char} (h : isWs t = false) : NoWs (t :: u) := by
  intro c t' hc
  injection hc with hcc
  rw [← hcc]
  exact h

/-! ## Numbers

A number is where the grammar is genuinely ambiguous about its remainder, so each part of one
carries the condition that pins it down: a run of digits must not be followed by a digit, a
fraction not by a point, an exponent not by an `e`. Each of those follows from `Follows` at the
end of the number, and in between from the shape of the part that comes after.
-/

@[expose] def NoDigit (l : List Char) : Prop := ∀ c t, l = c :: t → isDigit c = false

@[expose] def NoFrac (l : List Char) : Prop :=
  ∀ c t, l = c :: t → isDigit c = false ∧ c ≠ '.'

@[expose] def NoExp (l : List Char) : Prop :=
  ∀ c t, l = c :: t → isDigit c = false ∧ c ≠ 'e' ∧ c ≠ 'E'

/--
A whitespace character is one of the four the RFC lists. `isWs` is a disjunction of four
equalities, and this is what turns that `Bool` back into the case analysis a proof can walk
through.

`h : isWs c = true` says `c` passes the check, and the conclusion enumerates the four
possibilities: space, tab, line feed and carriage return. It is the definition read back, so
nothing new is proved; what it provides is the four cases in a form `rcases` can consume.
-/
theorem eq_of_isWs {c : Char} (h : isWs c = true) :
    c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\x0d' := by simpa [isWs, or_assoc] using h

/--
Nothing that may follow a value can begin an exponent. A number's exponent is optional, so a
derivation could otherwise try to read one from the text after the number has ended, and there
would be two ways to derive the same text.

`h : Follows l` says `l` is empty or begins with whitespace, a comma, a closing bracket or a
closing brace. `NoExp l` requires the leading character, if there is one, to be none of a digit,
`e` or `E`. Each character `Follows` permits is checked against all three, the whitespace case
being opened up by `eq_of_isWs`. The empty list satisfies both conditions with nothing to check,
which is a case rather than the whole content.
-/
theorem noExp_of_follows {l : List Char} (h : Follows l) : NoExp l := by
  intro c t hl
  rcases h c t hl with hw | rfl | rfl | rfl
  · rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide, by decide⟩
  all_goals exact ⟨by decide, by decide, by decide⟩

/--
Nothing that may follow a value can begin a fraction. The fraction is optional just as the
exponent is, so the same argument has to be made again for the decimal point; neither condition
implies the other.

`h : Follows l` says `l` is empty or begins with whitespace, a comma, a closing bracket or a
closing brace. `NoFrac l` requires the leading character, if there is one, to be neither a digit
nor `'.'`. Every permitted character is checked against both, the whitespace case through
`eq_of_isWs`.
-/
theorem noFrac_of_follows {l : List Char} (h : Follows l) : NoFrac l := by
  intro c t hl
  rcases h c t hl with hw | rfl | rfl | rfl
  · rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  all_goals exact ⟨by decide, by decide⟩

/--
A text that cannot begin a fraction cannot begin with a digit. The conditions on what may follow
the parts of a number are nested, and this is one of the two projections that let a stronger one
be used where a weaker is wanted.

`h : NoFrac l` says the leading character, if any, is neither a digit nor `'.'`, and `NoDigit l`
keeps only the first of those. It is a projection through the same quantifier, so it holds of the
empty list as vacuously as `NoFrac` does.
-/
theorem noDigit_of_noFrac {l : List Char} (h : NoFrac l) : NoDigit l :=
  fun c t hl => (h c t hl).1

/--
A text that cannot begin an exponent cannot begin with a digit. The exponent condition and the
fraction condition are independent, so the digit has to be extracted from each of them separately.

`h : NoExp l` says the leading character, if any, is none of a digit, `e` or `E`, and `NoDigit l`
keeps only the first conjunct. Which of the two projections a proof reaches for depends on which
of the two conditions it happens to be carrying at that point.
-/
theorem noDigit_of_noExp {l : List Char} (h : NoExp l) : NoDigit l :=
  fun c t hl => (h c t hl).1

/--
A run of digits begins with a digit. Every rejection proof has to know what each production can
start with, and this is that fact for `1*DIGIT`.

`h : Digits s v n r` says `s` begins with a run of digits. The conclusion produces a head `c` and
tail `t` with `s = c :: t` and `isDigit c = true`, so it also says `s` is not empty. Both
constructors put a digit at the front, so no case analysis beyond naming them is needed.
-/
theorem digits_head {s : List Char} {v n : Nat} {r : List Char} (h : Digits s v n r) :
    ∃ c t, s = c :: t ∧ isDigit c = true := by
  cases h with
  | last hd => exact ⟨_, _, rfl, hd⟩
  | cons hd _ => exact ⟨_, _, rfl, hd⟩

/--
No run of digits can be read where the text does not begin with a digit. This is what a rejection
proof actually uses, the positive form being awkward to apply against a hypothetical derivation.

`hc : isDigit c = false` says the leading character is not a digit, and `¬ Digits (c :: s) v n r`
denies every derivation, for any value, digit count and remainder. It follows by applying
`digits_head` to a supposed derivation, whose head must then be `c` itself.
-/
theorem not_digits_cons {c : Char} (hc : isDigit c = false) {s : List Char} {v n : Nat}
    {r : List Char} : ¬ Digits (c :: s) v n r := by
  intro h
  obtain ⟨c', t', hct, hd⟩ := digits_head h
  injection hct with hcc
  subst hcc
  rw [hc] at hd
  exact absurd hd (by decide)

/--
The integer part of a number begins with a digit. `Int'` has two constructors whose heads look
different, a literal `'0'` and a character between `1` and `9`, and this is what says both of them
are digits.

`h : Int' s v r` says `s` begins with an `int`. The conclusion produces a head and tail with
`s = c :: t` and `isDigit c = true`. The `zero` case is settled outright; the `digits` case has to
weaken `'1' ≤ c ∧ c ≤ '9'` to `'0' ≤ c ∧ c ≤ '9'`, which is where the ordering on
characters is actually used.
-/
theorem int_head {s : List Char} {v : Nat} {r : List Char} (h : Int' s v r) :
    ∃ c t, s = c :: t ∧ isDigit c = true := by
  cases h with
  | zero => exact ⟨_, _, rfl, by decide⟩
  | digits hc _ =>
    refine ⟨_, _, rfl, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Char.le_trans (by decide) hc.1, hc.2⟩

/--
A sign is either a leading minus or nothing at all, and the flag it carries says which. Reading a
number back out of a derivation means knowing exactly what the optional sign did, it being the
only part that can change the mantissa's sign.

`h : Sign l b r` says the front of `l` is an optional minus, `b` recording whether one was found.
The conclusion reads both constructors back: `b = false` with the text untouched, `r = l`, or
`b = true` with `l` being `'-'` followed by `r`. The two alternatives cannot both hold, since a
list is not its own tail.
-/
theorem sign_head {l : List Char} {b : Bool} {r : List Char} (h : Sign l b r) :
    (b = false ∧ r = l) ∨ (b = true ∧ l = '-' :: r) := by
  cases h with
  | absent => exact .inl ⟨rfl, rfl⟩
  | minus => exact .inr ⟨rfl, rfl⟩

/--
An exponent whose first character is an `e` really is an exponent, in one of its three forms.
Without this the `absent` alternative would be available at the same text, and a number could be
read back out of a derivation in two ways.

`h` is the derivation at a text beginning with `c`, `hc` says `c` is `'e'` or `'E'`, and
`hn : NoExp r` says nothing at the exponent's end could start another. Together they exclude
`Exp.absent`, which leaves `r` as the whole text and so would put `c` at the head of a list
`NoExp` forbids. What remains is the three-way disjunction: digits directly, digits after a `'+'`,
or digits after a `'-'` with the value negated.
-/
theorem exp_head {c : Char} {l : List Char} {e : Int} {r : List Char} (h : Exp (c :: l) e r)
    (hn : NoExp r) (hc : c = 'e' ∨ c = 'E') :
    (∃ v n, Digits l v n r ∧ e = (v : Int)) ∨
      (∃ u v n, l = '+' :: u ∧ Digits u v n r ∧ e = (v : Int)) ∨
        (∃ u v n, l = '-' :: u ∧ Digits u v n r ∧ e = -(v : Int)) := by
  cases h with
  | absent =>
    obtain ⟨-, he, hE⟩ := hn c l rfl
    rcases hc with rfl | rfl
    · exact absurd rfl he
    · exact absurd rfl hE
  | bare _ hd => exact .inl ⟨_, _, hd, rfl⟩
  | plus _ hd => exact .inr (.inl ⟨_, _, _, rfl, hd, rfl⟩)
  | minus _ hd => exact .inr (.inr ⟨_, _, _, rfl, hd, rfl⟩)

/--
A fraction that does not begin with a decimal point is not there at all, and contributes nothing.
Reading a number back needs an absent fraction to leave the mantissa and the digit count alone as
well as the text, and all three have to be said.

`h : Frac l f n r` and `hne`, which says `l` is not `'.'` followed by anything. The conclusion
gives `f = 0`, `n = 0` and `r = l` together. `Frac.present` requires the leading `'.'` that `hne`
denies, so only `absent` survives, and it fixes all three at once.
-/
theorem frac_absent {l : List Char} {f n : Nat} {r : List Char} (h : Frac l f n r)
    (hne : ∀ u, l ≠ '.' :: u) : f = 0 ∧ n = 0 ∧ r = l := by
  cases h with
  | absent => exact ⟨rfl, rfl, rfl⟩
  | present _ => exact absurd rfl (hne _)

/--
An exponent that does not begin with `e` or `E` is not there at all, and contributes nothing. It
is the exponent's counterpart to the fraction's, needed separately because an exponent has three
present forms rather than one.

`h : Exp l e r` and `hne`, which says the leading character, if there is one, is neither `'e'` nor
`'E'`. The conclusion is `e = 0` and `r = l`. All three present constructors begin with one of
those two characters, so `hne` excludes them and only `absent` remains; there is no digit count to
report, an exponent's digits not being carried by `Exp`.
-/
theorem exp_absent {l : List Char} {e : Int} {r : List Char} (h : Exp l e r)
    (hne : ∀ c u, l = c :: u → c ≠ 'e' ∧ c ≠ 'E') : e = 0 ∧ r = l := by
  cases h with
  | absent => exact ⟨rfl, rfl⟩
  | bare hE _ | plus hE _ | minus hE _ =>
    rcases hE with rfl | rfl
    · exact absurd rfl (hne _ _ rfl).1
    · exact absurd rfl (hne _ _ rfl).2

/--
A digit is not whitespace. The two character classes are defined independently of one another, so
their being disjoint is something to establish rather than something to assume.

`h : isDigit c = true` gives the classification, and `isWs c = false` denies the other. It is
proved by supposing `c` were whitespace, enumerating the four such characters through
`eq_of_isWs`, and checking that none of them is a digit.
-/
theorem isWs_of_isDigit {c : Char} (h : isDigit c = true) : isWs c = false := by
  cases hw : isWs c with
  | false => rfl
  | true => rcases eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact absurd h (by decide)

/--
A digit differs from any character that is not one. This is the shape a rejection proof wants,
where two characters have to be told apart by their classes rather than by their values.

`hc : isDigit c = true` and `hd : isDigit d = false` classify the two characters oppositely, and
`c ≠ d` follows, equal characters necessarily having equal classifications. Nothing about which
digit or which non-digit is used.
-/
theorem digit_ne {c d : Char} (hc : isDigit c = true) (hd : isDigit d = false) : c ≠ d := by
  rintro rfl
  rw [hd] at hc
  exact absurd hc (by decide)

/--
A number begins with a minus sign or a digit. This is what lets the value machine decide from one
character that a number follows, and what lets a rejection proof rule a number out.

`h : Num s n r` says `s` begins with a `number`. The conclusion produces a head and tail with
`s = c :: t` and `c = '-' ∨ isDigit c = true`. The sign is optional, so both alternatives arise:
with a sign the head is `'-'`, and without one it is the integer part's head, which `int_head`
says is a digit.
-/
theorem num_head {s : List Char} {n : Number} {r : List Char} (h : Num s n r) :
    ∃ c t, s = c :: t ∧ (c = '-' ∨ isDigit c = true) := by
  cases h with
  | mk hs hi _ _ =>
    cases hs with
    | absent =>
      obtain ⟨c, t, hct, hd⟩ := int_head hi
      exact ⟨c, t, hct, Or.inr hd⟩
    | minus => exact ⟨_, _, rfl, Or.inl rfl⟩

/--
No number can be read where the text begins with neither a minus nor a digit. It is the
contrapositive of what a number can begin with, and the direction the value rejection proof
applies.

`h₁ : c ≠ '-'` and `h₂ : isDigit c = false` between them exclude both alternatives that
`num_head` offers. The conclusion `¬ Num (c :: t) n r` denies every derivation, for any number
and any remainder.
-/
theorem not_num_cons {c : Char} {t : List Char} {n : Number} {r : List Char}
    (h₁ : c ≠ '-') (h₂ : isDigit c = false) : ¬ Num (c :: t) n r := by
  intro h
  obtain ⟨c', t', hct, hc⟩ := num_head h
  injection hct with hcc
  subst hcc
  rcases hc with rfl | hd
  · exact h₁ rfl
  · rw [h₂] at hd
    exact absurd hd (by decide)

/--
The text at which a number's exponent begins cannot begin a fraction. Reading a number back means
recovering the boundary between its fraction and its exponent, and that boundary is fixed by the
fraction being unable to continue past it.

`he : Exp c e r` places the exponent from `c` to `r` and `hr : Follows r` says the number has
ended at `r`. The conclusion `NoFrac c` says `c` begins with neither a digit nor a `'.'`. Where
the exponent is present, `c` begins with `'e'` or `'E'`, which is neither; where it is absent, `c`
is `r` itself and `noFrac_of_follows` supplies the conclusion.
-/
theorem noFrac_after_exp {c r : List Char} {e : Int} (he : Exp c e r) (hr : Follows r) :
    NoFrac c := by
  cases he with
  | absent => exact noFrac_of_follows hr
  | bare hE _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    rcases hE with rfl | rfl <;> exact ⟨by decide, by decide⟩
  | plus hE _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    rcases hE with rfl | rfl <;> exact ⟨by decide, by decide⟩
  | minus hE _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    rcases hE with rfl | rfl <;> exact ⟨by decide, by decide⟩

/--
The text at which a number's integer part ends cannot begin with a digit. Without this a run of
digits could be cut anywhere, and `12` would derive as `1` followed by a leftover `2` with exactly
the same standing as `12`.

`hf : Frac b f nf c` places the fraction from `b` to `c`, `he : Exp c e r` the exponent from `c`
to `r`, and `hr : Follows r` says the number has ended. The conclusion `NoDigit b` says `b` does
not begin with a digit. With a fraction present, `b` begins with `'.'`; with it absent, `b` is `c`
itself, and `noFrac_after_exp` followed by `noDigit_of_noFrac` gives the result.
-/
theorem noDigit_after_int {b c r : List Char} {f nf : Nat} {e : Int}
    (hf : Frac b f nf c) (he : Exp c e r) (hr : Follows r) : NoDigit b := by
  cases hf with
  | present _ =>
    intro c' t' h
    injection h with hcc
    subst hcc
    decide
  | absent => exact noDigit_of_noFrac (noFrac_after_exp he hr)

/-! ## Strings

The closing quotation mark is a character no `Ch` can begin with, which is what ends a string
without any condition on what follows it.
-/

@[expose] def NoCh (l : List Char) : Prop := ∀ c r, ¬ Ch l c r

/--
A quotation mark cannot begin a character of a string literal. That is what ends a string: the
closing quote is the one character the body cannot swallow, so the string production needs no
condition on what follows it, unlike the number productions.

`NoCh ('"' :: t)` denies every `Ch` derivation from a text beginning with `'"'`, for any character
and any remainder. Only `Ch.unescaped` could apply, `'"'` being no backslash, and `isUnescaped`
excludes the quotation mark by construction, which is checked here by `decide`.
-/
theorem noCh_quote {t : List Char} : NoCh ('"' :: t) := by
  intro c r h
  cases h with
  | unescaped hu => exact absurd hu (by decide)

/--
A string literal begins with a quotation mark. It is the one-character signal the value machine
dispatches on, and the fact a rejection proof needs in order to rule a string out.

`h : Str s v r` says `s` begins with a string literal denoting `v`. The conclusion produces the
tail `t` with `s = '"' :: t`. `Str` has a single constructor, which writes the opening quotation
mark explicitly, so nothing remains but to name the tail.
-/
theorem str_head {s : List Char} {v : String} {r : List Char} (h : Str s v r) :
    ∃ t, s = '"' :: t := by cases h with | mk _ => exact ⟨_, rfl⟩

/--
No string literal can be read where the text does not begin with a quotation mark. The
contrapositive of what a string begins with, in the form the value rejection proof uses.

`hne : c ≠ '"'` is the only hypothesis, and `¬ Str (c :: t) v r` denies every derivation, for
any string value and remainder. `Str`'s single constructor demands the quotation mark that `hne`
withholds.
-/
theorem not_str_cons {c : Char} {t : List Char} {v : String} {r : List Char}
    (hne : c ≠ '"') : ¬ Str (c :: t) v r := by
  intro h
  cases h with
  | mk _ => exact hne rfl

/-! ## Values -/

/--
No array can be read where the text begins with a non-whitespace character other than `[`. The
opening bracket is surrounded by whitespace in the grammar, so ruling an array out means also
ruling out that the whitespace could have hidden the bracket.

`hw : isWs c = false` and `hne : c ≠ '['` are both needed: without the first, the leading
whitespace could consume `c` and find a bracket behind it. The conclusion denies both
constructors, `empty` and `items`, each of which opens with a `BeginArray` token that
`not_token_of_ne` excludes.
-/
theorem not_arr_cons {c : Char} {t : List Char} {e : Array Json} {r : List Char}
    (hw : isWs c = false) (hne : c ≠ '[') : ¬ Arr (c :: t) e r := by
  intro h
  cases h with
  | empty hb _ => exact not_token_of_ne hw hne hb
  | items hb _ _ => exact not_token_of_ne hw hne hb

/--
No object can be read where the text begins with a non-whitespace character other than `{`. It is
the object's counterpart to the array case, needed separately because the two productions are
distinct and open on different characters.

`hw : isWs c = false` and `hne : c ≠ '{'` are again both needed, for the same reason. The
conclusion denies both `empty` and `members`, each opening with a `BeginObject` token that
`not_token_of_ne` excludes.
-/
theorem not_obj_cons {c : Char} {t : List Char} {f : Array (String × Json)}
    {r : List Char} (hw : isWs c = false) (hne : c ≠ '{') : ¬ Object (c :: t) f r := by
  intro h
  cases h with
  | empty hb _ => exact not_token_of_ne hw hne hb
  | members hb _ _ => exact not_token_of_ne hw hne hb

/--
No value can be read where the text begins with a character that none of the seven alternatives
can start with. This is the grammar's whole rejection at a single character, and it is what a
parser's "unexpected character" error has to be justified against.

`hw` says the character is not whitespace, which is what the two container cases need, and the
remaining hypotheses exclude the leading characters of the other alternatives: `'f'`, `'n'`,
`'t'`, `'"'`, `'['`, `'{'`, and a minus or a digit for a number. The conclusion denies every
derivation, for any value and remainder. Each alternative is dispatched by its own hypothesis, the
number through `not_num_cons` and the containers through `not_arr_cons` and `not_obj_cons`.
-/
theorem not_value_cons {c : Char} {t : List Char} {j : Json} {r : List Char}
    (hw : isWs c = false) (hf : c ≠ 'f') (hn : c ≠ 'n') (ht : c ≠ 't') (hq : c ≠ '"')
    (hb : c ≠ '[') (hc : c ≠ '{') (hm : c ≠ '-') (hd : isDigit c = false) :
    ¬ Value (c :: t) j r := by
  intro h
  cases h with
  | false_ => exact hf rfl
  | null => exact hn rfl
  | true_ => exact ht rfl
  | str hs => cases hs with | mk _ => exact hq rfl
  | num hn' => exact not_num_cons hm hd hn'
  | arr ha => exact not_arr_cons hw hb ha
  | obj ho => exact not_obj_cons hw hc ho

/--
No value begins with a closing bracket. It is the instance of the general rejection that the array
productions need, where a `]` at the head of the text has to mean the array has ended rather than
that a further element follows.

`¬ Value (']' :: t) j r` denies every derivation, for any value and remainder. It is
`not_value_cons` with all nine hypotheses discharged by `decide` at the character `']'`, which is
neither whitespace nor any of the eight characters a value can begin with.
-/
theorem not_value_bracket {t : List Char} {j : Json} {r : List Char} :
    ¬ Value (']' :: t) j r :=
  not_value_cons (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

/--
A list of array elements cannot begin with a closing bracket. This is what makes `[1,]` a
rejection rather than a parse: after a comma the grammar demands an element, and a `]` cannot
supply one.

`¬ Elements (']' :: t) vs r` denies every derivation, for any list of values and remainder. Both
constructors, `one` and `more`, begin with a `Value`, and `not_value_bracket` denies that at this
text.
-/
theorem not_elements_bracket {t : List Char} {vs : List Json} {r : List Char} :
    ¬ Elements (']' :: t) vs r := by
  intro h
  cases h with
  | one hv => exact not_value_bracket hv
  | more hv _ _ => exact not_value_bracket hv

/--
A list of object members cannot begin with a closing brace. The counterpart for objects:
`{"a":1,}` is refused because after a comma a member is required, and a `}` cannot begin one.

`¬ Members ('}' :: t) ms r` denies every derivation, for any list of fields and remainder. Both
constructors begin with a `Member`, which begins with a `Str`, which requires a quotation mark;
the argument therefore runs through `Str`'s single constructor rather than through the general
value rejection.
-/
theorem not_members_brace {t : List Char} {ms : List (String × Json)} {r : List Char} :
    ¬ Members ('}' :: t) ms r := by
  intro h
  cases h with
  | one hm => cases hm with | mk hs _ _ => cases hs
  | more hm _ _ => cases hm with | mk hs _ _ => cases hs

/--
An array's text reaches a `[` after some whitespace. Where the rejection lemmas say what an array
cannot begin with, this says what it does begin with, which is what a proof that consumes the
leading whitespace first has to know.

`h : Arr s e r` says `s` begins with an `array` production. The conclusion produces a `u` with
`Ws s ('[' :: u)`, so a whitespace run from `s` stops exactly at the opening bracket. Both
constructors carry a `BeginArray`, which is whitespace, the bracket, then whitespace, and it is
the first part of that which is extracted here.
-/
theorem arr_begin {s : List Char} {e : Array Json} {r : List Char} (h : Arr s e r) :
    ∃ u, Ws s ('[' :: u) := by
  cases h with
  | empty hb _ => cases hb with | mk w _ => exact ⟨_, w⟩
  | items hb _ _ => cases hb with | mk w _ => exact ⟨_, w⟩

/--
An object's text reaches a `{` after some whitespace. The object's counterpart to the array case,
and needed in the same places: wherever a proof has skipped whitespace and must know what it is
now looking at.

`h : Object s f r` says `s` begins with an `object` production. The conclusion produces a `u` with
`Ws s ('{' :: u)`, so a whitespace run from `s` stops at the opening brace. Both constructors
carry a `BeginObject`, whose leading whitespace is what is extracted.
-/
theorem obj_begin {s : List Char} {f : Array (String × Json)} {r : List Char}
    (h : Object s f r) : ∃ u, Ws s ('{' :: u) := by
  cases h with
  | empty hb _ => cases hb with | mk w _ => exact ⟨_, w⟩
  | members hb _ _ => cases hb with | mk w _ => exact ⟨_, w⟩

/--
Text at a separator or a closing bracket is text a value may be followed by. `Follows` is the
condition that ends a number, and this is how it is discharged wherever a value is known to be
followed by one of those three characters.

`h : Token t s r` says the token was read from `s`, and `ht` confines `t` to `','`, `']'` or
`'}'`. The conclusion `Follows s` says `s` is empty or begins with whitespace or one of those
three. The token's leading whitespace is where the two cases come from: if it consumed nothing the
head of `s` is `t` itself, and if it consumed something the head is whitespace.
-/
theorem follows_of_token {t : Char} {s r : List Char} (h : Token t s r)
    (ht : t = ',' ∨ t = ']' ∨ t = '}') : Follows s := by
  intro c t' hs
  subst hs
  cases h with
  | mk w _ =>
    cases w with
    | nil =>
      rcases ht with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    | cons hc _ => exact Or.inl hc

/--
Text at the end of a document is text a value may be followed by. A number at the very end of the
text has nothing after it at all, and `Follows` has to be discharged there as well as at a
separator.

`h : Ws l []` says whitespace consumes the whole of `l`. `Follows l` says `l` is empty or begins
with whitespace, a comma, a closing bracket or a closing brace. Where `l` is empty there is
nothing to check; otherwise the run must have taken `l`'s head, so that head is whitespace and the
first disjunct holds.
-/
theorem follows_of_ws {l : List Char} (h : Ws l []) : Follows l := by
  intro c t hl
  subst hl
  cases h with
  | cons hc _ => exact Or.inl hc

end Json.Spec
