/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec
public import Json.Spec.Follow
public import Json.Spec.Length

public section

namespace Json.Spec

/-!
The grammar names at most one value for a text.

This is a claim about the transcription rather than about the parser: a grammar that derived two
values for one text would make "the value the text denotes" meaningless, and no proof about the
parser could repair it.

The relations are deliberately not deterministic in their remainder, exactly as the ABNF is not:
`12` derives as `1` with `2` left over as readily as it derives as `12`. Two things pin that
down. A value is followed either by the end of the text or by one of the characters that
separates or closes, which is what `Follows` says, and that is enough to make the value unique.
Whitespace is the other: `ws` appears on both sides of every structural character, so two
derivations of the same text can divide one run of spaces differently, and `Json.Spec.Follow`
says that they still reach the same place whenever what comes next is not whitespace.
-/

/-! ## Numbers

A number is where the grammar is genuinely ambiguous about its remainder, so each part of one is
unique only once its remainder is pinned down, which is what `Json.Spec.Follow` supplies: a run
of digits must not be followed by a digit, a fraction not by a point, an exponent not by an `e`.
-/

/--
A run of digits has one reading, once it is known not to be followed by another digit. The grammar
is genuinely ambiguous here: `12` derives as `1` with `2` left over as readily as it derives as
`12`, so without a condition on what follows there is no single answer to give.

`h₁` and `h₂` are two derivations from the same `s`, and `hn₁`, `hn₂` say neither
remainder begins with a digit. The conclusion `v₁ = v₂ ∧ n₁ = n₂ ∧ r₁ = r₂` fixes
the value, the digit count and the remainder together. The two `NoDigit` conditions are what
exclude the mismatched cases, where one derivation stopped and the other went on; `digits_head`
turns that continuation into a digit the condition forbids.
-/
theorem digits_unique {s : List Char} {v₁ n₁ : Nat} {r₁ : List Char}
    (h₁ : Digits s v₁ n₁ r₁) : ∀ {v₂ n₂ : Nat} {r₂ : List Char}, Digits s v₂ n₂ r₂ →
      NoDigit r₁ → NoDigit r₂ → v₁ = v₂ ∧ n₁ = n₂ ∧ r₁ = r₂ := by
  induction h₁ with
  | @last c r hd =>
    intro v₂ n₂ r₂ h₂ hn₁ _
    cases h₂ with
    | last => exact ⟨rfl, rfl, rfl⟩
    | cons _ h₂' =>
      obtain ⟨c', t', hct, hd'⟩ := digits_head h₂'
      rw [hct] at hn₁
      rw [hn₁ c' t' rfl] at hd'
      exact absurd hd' (by decide)
  | @cons c s v n r hd h₁' ih =>
    intro v₂ n₂ r₂ h₂ hn₁ hn₂
    cases h₂ with
    | last =>
      obtain ⟨c', t', hct, hd'⟩ := digits_head h₁'
      rw [hct] at hn₂
      rw [hn₂ c' t' rfl] at hd'
      exact absurd hd' (by decide)
    | cons _ h₂' =>
      obtain ⟨hv, hn, hr⟩ := ih h₂' hn₁ hn₂
      exact ⟨by rw [hv, hn], by rw [hn], hr⟩

/--
The integer part of a number has one reading, once it is known not to be followed by a digit. The
ABNF gives a leading zero its own case, so `01` is not one integer, and this says among other
things that the two cases cannot both apply to one text.

`h₁` and `h₂` are two `Int'` derivations from `s`, and `hn₁`, `hn₂` say neither remainder
begins with a digit. The conclusion is `v₁ = v₂ ∧ r₁ = r₂`. The `zero` and `digits`
constructors are told apart by their leading character, `'0'` against `'1'` to `'9'`, which
`decide` settles; where both are `digits`, `digits_unique` under the same two conditions finishes
it.
-/
private theorem int_unique {s : List Char} {v₁ v₂ : Nat} {r₁ r₂ : List Char}
    (h₁ : Int' s v₁ r₁) (h₂ : Int' s v₂ r₂) (hn₁ : NoDigit r₁) (hn₂ : NoDigit r₂) :
    v₁ = v₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | zero =>
    cases h₂ with
    | zero => exact ⟨rfl, rfl⟩
    | digits hc _ => exact absurd hc (by decide)
  | digits hc₁ hd₁ =>
    cases h₂ with
    | zero => exact absurd hc₁ (by decide)
    | digits _ hd₂ =>
      obtain ⟨hv, _, hr⟩ := digits_unique hd₁ hd₂ hn₁ hn₂
      exact ⟨hv, hr⟩

/--
A fraction has one reading, once it is known not to be followed by a digit or a decimal point. It
is optional, so the point is what distinguishes a fraction that is there from one that is not, and
its digits need the same condition as any other run.

`h₁` and `h₂` are two `Frac` derivations from `s`, and `hn₁`, `hn₂` are `NoFrac` on the
two remainders, forbidding both a digit and a `'.'`. The conclusion gives the value, the digit
count and the remainder. The mixed cases, one fraction present and the other absent, are excluded
by the `'.'` half of the condition; the case where both are present reduces to `digits_unique`
through `noDigit_of_noFrac`.
-/
private theorem frac_unique {s : List Char} {f₁ n₁ f₂ n₂ : Nat} {r₁ r₂ : List Char}
    (h₁ : Frac s f₁ n₁ r₁) (h₂ : Frac s f₂ n₂ r₂) (hn₁ : NoFrac r₁) (hn₂ : NoFrac r₂) :
    f₁ = f₂ ∧ n₁ = n₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | absent =>
    cases h₂ with
    | absent => exact ⟨rfl, rfl, rfl⟩
    | present _ => exact absurd rfl (hn₁ _ _ rfl).2
  | present hd₁ =>
    cases h₂ with
    | absent => exact absurd rfl (hn₂ _ _ rfl).2
    | present hd₂ =>
      exact digits_unique hd₁ hd₂ (noDigit_of_noFrac hn₁) (noDigit_of_noFrac hn₂)

/--
An exponent has one reading, once it is known not to be followed by a digit or by an `e`. It has
four constructors, one absent and three present, which makes it the widest case analysis among the
number productions.

`h₁` and `h₂` are two `Exp` derivations from `s`, and `hn₁`, `hn₂` are `NoExp` on the
remainders, forbidding a digit, an `'e'` and an `'E'`. The conclusion is
`e₁ = e₂ ∧ r₁ = r₂`. The absent case is separated from the three present ones by the
`'e'` and `'E'` halves of the condition; the three present ones are separated from each other by
whether a `'+'` or a `'-'` follows, through `not_digits_cons`, a sign not being a digit.
-/
private theorem exp_unique {s : List Char} {e₁ e₂ : Int} {r₁ r₂ : List Char}
    (h₁ : Exp s e₁ r₁) (h₂ : Exp s e₂ r₂) (hn₁ : NoExp r₁) (hn₂ : NoExp r₂) :
    e₁ = e₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | absent =>
    cases h₂ with
    | absent => exact ⟨rfl, rfl⟩
    | bare he _ => rcases he with rfl | rfl
                   · exact absurd rfl (hn₁ _ _ rfl).2.1
                   · exact absurd rfl (hn₁ _ _ rfl).2.2
    | plus he _ => rcases he with rfl | rfl
                   · exact absurd rfl (hn₁ _ _ rfl).2.1
                   · exact absurd rfl (hn₁ _ _ rfl).2.2
    | minus he _ => rcases he with rfl | rfl
                    · exact absurd rfl (hn₁ _ _ rfl).2.1
                    · exact absurd rfl (hn₁ _ _ rfl).2.2
  | bare he₁ hd₁ =>
    cases h₂ with
    | absent => rcases he₁ with rfl | rfl
                · exact absurd rfl (hn₂ _ _ rfl).2.1
                · exact absurd rfl (hn₂ _ _ rfl).2.2
    | bare _ hd₂ =>
      obtain ⟨hv, _, hr⟩ :=
        digits_unique hd₁ hd₂ (noDigit_of_noExp hn₁) (noDigit_of_noExp hn₂)
      exact ⟨by rw [hv], hr⟩
    | plus _ _ => exact absurd hd₁ (not_digits_cons (by decide))
    | minus _ _ => exact absurd hd₁ (not_digits_cons (by decide))
  | plus he₁ hd₁ =>
    cases h₂ with
    | absent => rcases he₁ with rfl | rfl
                · exact absurd rfl (hn₂ _ _ rfl).2.1
                · exact absurd rfl (hn₂ _ _ rfl).2.2
    | bare _ hd₂ => exact absurd hd₂ (not_digits_cons (by decide))
    | plus _ hd₂ =>
      obtain ⟨hv, _, hr⟩ :=
        digits_unique hd₁ hd₂ (noDigit_of_noExp hn₁) (noDigit_of_noExp hn₂)
      exact ⟨by rw [hv], hr⟩
  | minus he₁ hd₁ =>
    cases h₂ with
    | absent => rcases he₁ with rfl | rfl
                · exact absurd rfl (hn₂ _ _ rfl).2.1
                · exact absurd rfl (hn₂ _ _ rfl).2.2
    | bare _ hd₂ => exact absurd hd₂ (not_digits_cons (by decide))
    | minus _ hd₂ =>
      obtain ⟨hv, _, hr⟩ :=
        digits_unique hd₁ hd₂ (noDigit_of_noExp hn₁) (noDigit_of_noExp hn₂)
      exact ⟨by rw [hv], hr⟩

/--
A number's sign has one reading, and what settles it is the integer part that comes after rather
than any condition on the remainder. That part must begin with a digit, and a minus is not one,
which is enough to tell a sign that is there from one that is not.

`h₁` and `h₂` are two `Sign` derivations from `s`, and `hi₁`, `hi₂` are the integer parts
that follow each of them. The conclusion `b₁ = b₂ ∧ a₁ = a₂` fixes both the flag and the
text the integer part starts at. The integer hypotheses earn their place in the mixed cases: there
one derivation would have the integer part begin at the `'-'`, which `int_head` says is a digit
and `decide` says is not.
-/
private theorem sign_unique {s : List Char} {b₁ b₂ : Bool} {a₁ a₂ : List Char} {i₁ i₂ : Nat}
    {t₁ t₂ : List Char} (h₁ : Sign s b₁ a₁) (h₂ : Sign s b₂ a₂)
    (hi₁ : Int' a₁ i₁ t₁) (hi₂ : Int' a₂ i₂ t₂) : b₁ = b₂ ∧ a₁ = a₂ := by
  cases h₁ with
  | absent =>
    cases h₂ with
    | absent => exact ⟨rfl, rfl⟩
    | minus =>
      obtain ⟨c, t, hct, hd⟩ := int_head hi₁
      injection hct with hcc
      subst hcc
      exact absurd hd (by decide)
  | minus =>
    cases h₂ with
    | absent =>
      obtain ⟨c, t, hct, hd⟩ := int_head hi₂
      injection hct with hcc
      subst hcc
      exact absurd hd (by decide)
    | minus => exact ⟨rfl, rfl⟩

/--
A number has one reading, once it is known what may follow it. This is the ambiguity the ABNF
genuinely carries, and `Follows` is what resolves it: nothing that can come after a value in a
well-formed text can continue a number.

`h₁` and `h₂` are two `Num` derivations from `s`, and `f₁`, `f₂` say each remainder is
empty or begins with whitespace, a comma, or a closing bracket or brace. The conclusion
`n₁ = n₂ ∧ r₁ = r₂` fixes both the number and where it ended. The four parts are settled
in order: the sign by `sign_unique`, the integer part by `int_unique` under `noDigit_after_int`,
the fraction by `frac_unique` under `noFrac_after_exp`, and the exponent by `exp_unique` under
`noExp_of_follows`. Each of those conditions is derived from `Follows` by working backwards from
the end of the number.
-/
theorem num_unique {s : List Char} {n₁ n₂ : Number} {r₁ r₂ : List Char}
    (h₁ : Num s n₁ r₁) (h₂ : Num s n₂ r₂) (f₁ : Follows r₁) (f₂ : Follows r₂) :
    n₁ = n₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | mk hs₁ hi₁ hfr₁ hex₁ =>
    cases h₂ with
    | mk hs₂ hi₂ hfr₂ hex₂ =>
      obtain ⟨hb, ha⟩ := sign_unique hs₁ hs₂ hi₁ hi₂
      subst ha
      obtain ⟨hiv, hbb⟩ :=
        int_unique hi₁ hi₂ (noDigit_after_int hfr₁ hex₁ f₁) (noDigit_after_int hfr₂ hex₂ f₂)
      subst hbb
      obtain ⟨hfv, hnf, hcc⟩ :=
        frac_unique hfr₁ hfr₂ (noFrac_after_exp hex₁ f₁) (noFrac_after_exp hex₂ f₂)
      subst hcc
      obtain ⟨hev, hr⟩ := exp_unique hex₁ hex₂ (noExp_of_follows f₁) (noExp_of_follows f₂)
      refine ⟨?_, hr⟩
      rw [hb, hiv, hfv, hnf, hev]


/-! ## Strings

A string needs no condition on what follows it, because the closing quotation mark is a character
no `Ch` can begin with. The one place two constructors could both apply is a `\u` escape, and
what separates them is that no character carries a surrogate code point: a four-digit escape in
the surrogate range denotes nothing on its own, so only the pair rule can derive it.
-/

/--
Four hexadecimal digits have one reading. `Hex4` matches a fixed number of characters, which makes
it the one production whose uniqueness needs no condition on what follows it and no induction.

`h₁` and `h₂` are two derivations from `s`, and the conclusion is
`v₁ = v₂ ∧ r₁ = r₂`. Both derivations match the same four characters, and `hexVal?` is a
function, so they record the same four values; the remainder is what is left after exactly four
characters either way.
-/
private theorem hex4_unique {s : List Char} {v₁ v₂ : Nat} {r₁ r₂ : List Char}
    (h₁ : Hex4 s v₁ r₁) (h₂ : Hex4 s v₂ r₂) : v₁ = v₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | mk a₁ b₁ c₁ d₁ =>
    cases h₂ with
    | mk a₂ b₂ c₂ d₂ =>
      rw [a₁] at a₂
      rw [b₁] at b₂
      rw [c₁] at c₂
      rw [d₁] at d₂
      injection a₂ with a
      injection b₂ with b
      injection c₂ with c
      injection d₂ with d
      subst a
      subst b
      subst c
      subst d
      exact ⟨rfl, rfl⟩

/--
One character of a string literal has one reading. The escapes all share a leading backslash and
the two `\u` rules share their first six characters, so this is where the grammar comes closest to
being ambiguous, and where it is saved by no `Char` carrying a surrogate code point.

`h₁` and `h₂` are two `Ch` derivations from `s`, and `c₁ = c₂ ∧ r₁ = r₂` holds with
no side condition, each constructor fixing its own leading characters. `unescaped` is separated
from every escape by `isUnescaped` excluding the backslash. The interesting pair is `codePoint`
against `surrogatePair`: both begin `\u`, and `hex4_unique` makes them agree on the four digits,
so what separates them is `char_not_surrogate`, `codePoint` having to name a character whose code
point lies in the very range `surrogatePair` requires.
-/
private theorem ch_unique {s : List Char} {c₁ c₂ : Char} {r₁ r₂ : List Char}
    (h₁ : Ch s c₁ r₁) (h₂ : Ch s c₂ r₂) : c₁ = c₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | unescaped hu =>
    cases h₂ with
    | unescaped => exact ⟨rfl, rfl⟩
    | _ => exact absurd hu (by decide)
  | quote =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | quote => exact ⟨rfl, rfl⟩
  | backslash =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | backslash => exact ⟨rfl, rfl⟩
  | solidus =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | solidus => exact ⟨rfl, rfl⟩
  | backspace =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | backspace => exact ⟨rfl, rfl⟩
  | formFeed =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | formFeed => exact ⟨rfl, rfl⟩
  | lineFeed =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | lineFeed => exact ⟨rfl, rfl⟩
  | carriageReturn =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | carriageReturn => exact ⟨rfl, rfl⟩
  | tab =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | tab => exact ⟨rfl, rfl⟩
  | codePoint hx₁ hv₁ =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | codePoint hx₂ hv₂ =>
      obtain ⟨hv, hr⟩ := hex4_unique hx₁ hx₂
      exact ⟨Char.toNat_inj.mp (by rw [hv₁, hv₂, hv]), hr⟩
    | surrogatePair hx₂ _ hhi₁ hhi₂ _ _ _ =>
      obtain ⟨hv, _⟩ := hex4_unique hx₁ hx₂
      rcases char_not_surrogate c₁ with h | h <;> omega
  | surrogatePair hx₁ hlo₁ hhi₁ hhi₂ hlo₃ hlo₄ hc₁ =>
    cases h₂ with
    | unescaped hu => exact absurd hu (by decide)
    | codePoint hx₂ hv₂ =>
      obtain ⟨hv, _⟩ := hex4_unique hx₁ hx₂
      rcases char_not_surrogate c₂ with h | h <;> omega
    | surrogatePair hx₂ hlo₂ _ _ _ _ hc₂ =>
      obtain ⟨hvhi, hrhi⟩ := hex4_unique hx₁ hx₂
      injection hrhi with _ hrhi'
      injection hrhi' with _ hrhi''
      subst hrhi''
      obtain ⟨hvlo, hr⟩ := hex4_unique hlo₁ hlo₂
      exact ⟨Char.toNat_inj.mp (by rw [hc₁, hc₂, hvhi, hvlo]), hr⟩

/--
A run of string characters has one reading, once it is known that no further character can be
taken. The run is greedy only because of that condition; without it a literal's body could stop
anywhere inside itself.

`h₁` and `h₂` are two `Chars` derivations from `s`, and `hn₁`, `hn₂` say neither remainder
can begin a `Ch`. The conclusion `cs₁ = cs₂ ∧ r₁ = r₂` fixes both the characters and
where the run stopped. The mismatched cases, one run empty and the other not, are excluded by the
`NoCh` condition on the empty one; the matching case is `ch_unique` followed by the induction
hypothesis.
-/
private theorem chars_unique {s : List Char} {cs₁ : List Char} {r₁ : List Char}
    (h₁ : Chars s cs₁ r₁) : ∀ {cs₂ r₂ : List Char}, Chars s cs₂ r₂ →
      NoCh r₁ → NoCh r₂ → cs₁ = cs₂ ∧ r₁ = r₂ := by
  induction h₁ with
  | nil =>
    intro cs₂ r₂ h₂ hn₁ _
    cases h₂ with
    | nil => exact ⟨rfl, rfl⟩
    | cons hch _ => exact absurd hch (hn₁ _ _)
  | @cons s s' cs c r hch _ ih =>
    intro cs₂ r₂ h₂ hn₁ hn₂
    cases h₂ with
    | nil => exact absurd hch (hn₂ _ _)
    | cons hch₂ h₂' =>
      obtain ⟨hc, hs⟩ := ch_unique hch hch₂
      subst hc
      subst hs
      obtain ⟨hcs, hr⟩ := ih h₂' hn₁ hn₂
      exact ⟨by rw [hcs], hr⟩

/--
A string literal has one reading, with no condition at all on what follows it. That sets it apart
from a number: the closing quotation mark is a character no `Ch` can begin with, so the literal
ends where it ends whatever comes next.

`h₁` and `h₂` are two `Str` derivations from `s`, and the conclusion is
`v₁ = v₂ ∧ r₁ = r₂`. `chars_unique` settles the body, and its two `NoCh` conditions are
both discharged by `noCh_quote`, each derivation being required to stop its body at a `'"'`. The
final `injection` is what strips that quotation mark off the remainder.
-/
theorem str_unique {s : List Char} {v₁ v₂ : String} {r₁ r₂ : List Char}
    (h₁ : Str s v₁ r₁) (h₂ : Str s v₂ r₂) : v₁ = v₂ ∧ r₁ = r₂ := by
  cases h₁ with
  | mk hcs₁ =>
    cases h₂ with
    | mk hcs₂ =>
      obtain ⟨hcs, hr⟩ := chars_unique hcs₁ hcs₂ noCh_quote noCh_quote
      injection hr with _ hr'
      exact ⟨by rw [hcs], hr'⟩


/-! ## Values

Two derivations of the same text can divide a run of whitespace differently, so the remainders
they reach need not be equal: `[] ` derives with a space left over or with nothing left over.
What holds is that one remainder is the other with some whitespace taken off, which is `WsEq`,
and that is enough, because the production that follows begins with a character that is not
whitespace and so starts in the same place either way.
-/

private def WsEq (a b : List Char) : Prop := Ws a b ∨ Ws b a

/--
Every text stands in the whitespace relation to itself. Two derivations of one text may leave
remainders that differ by some whitespace, which is what `WsEq` records, and a proof comparing a
text with itself needs the reflexive case of it.

`WsEq a b` is `Ws a b ∨ Ws b a`, one remainder reachable from the other by whitespace.
`WsEq a a` takes the left disjunct with `Ws.nil`, the run that consumes nothing. Nothing about `a`
is used, so it holds of every text.
-/
private theorem WsEq.refl (a : List Char) : WsEq a a := Or.inl Ws.nil

/--
Whitespace on either side of a structural character does not move the character. Two derivations
may divide a run of spaces differently, and this is what says they nonetheless arrive at the same
bracket, with the same text behind it.

`h : WsEq a b` says the two starting points differ only by whitespace, `h₁` and `h₂` are runs
reaching a leading character in each, and `n₁`, `n₂` say those two characters are not
themselves whitespace. The conclusion `t₁ = t₂ ∧ u₁ = u₂` says the character and
everything after it agree. The two non-whitespace conditions are what `Ws.eq_of_noWs` needs in
order to place both runs at the same character; without them the runs could stop at different
points in the same text.
-/
private theorem wsEq_token_eq {a b : List Char} {t₁ t₂ : Char} {u₁ u₂ : List Char}
    (h : WsEq a b) (h₁ : Ws a (t₁ :: u₁)) (h₂ : Ws b (t₂ :: u₂))
    (n₁ : isWs t₁ = false) (n₂ : isWs t₂ = false) : t₁ = t₂ ∧ u₁ = u₂ := by
  have key : ∀ {s : List Char}, Ws s (t₁ :: u₁) → Ws s (t₂ :: u₂) → t₁ = t₂ ∧ u₁ = u₂ := by
    intro s k₁ k₂
    have he := Ws.eq_of_noWs k₁ k₂ (noWs_cons n₁) (noWs_cons n₂)
    injection he with ht hu
    exact ⟨ht, hu⟩
  rcases h with hab | hba
  · exact key h₁ (hab.trans h₂)
  · exact key (hba.trans h₁) h₂

/--
A token can still be read after some of its leading whitespace has already been skipped. Every
structural character carries whitespace on both sides, so a proof that has consumed part of a run
must be able to hand the rest to a derivation that expects the whole of it.

`hw : Ws x y` says whitespace took `x` to `y`, `h : Token t x r` reads the token from `x`, and
`hnw` says the token's own character is not whitespace. `Token t y r` reads the same token from
the shortened text with the same remainder. Confluence puts `y` and the token's leading run in one
order or the other; where `y` is the further on, `ws_eq_of_not_isWs` says nothing more can have
been taken, and `hnw` is what makes that so.
-/
theorem token_ws {x y : List Char} {t : Char} {r : List Char} (hnw : isWs t = false)
    (hw : Ws x y) (h : Token t x r) : Token t y r := by
  cases h with
  | mk h₁ h₂ =>
    rcases hw.confluent h₁ with hc | hc
    · exact Token.mk hc h₂
    · exact Token.mk (by rw [ws_eq_of_not_isWs hnw hc]; exact Ws.nil) h₂

/--
An array can still be read after some leading whitespace has been skipped. The array production
opens with a token whose own whitespace absorbs what was taken, and this carries that through both
of its constructors.

`hw : Ws x y` says whitespace took `x` to `y`, and `h : Arr x e r` derives an array from `x`. The
conclusion `Arr y e r` derives the same elements with the same remainder from `y`. Both `empty`
and `items` open with a `BeginArray`, which `token_ws` moves, `decide` supplying that `'['` is not
whitespace; the rest of each derivation is carried across untouched.
-/
theorem arr_ws {x y : List Char} {e : Array Json} {r : List Char} (hw : Ws x y)
    (h : Arr x e r) : Arr y e r := by
  cases h with
  | empty hb he => exact Arr.empty (token_ws (by decide) hw hb) he
  | items hb hel he => exact Arr.items (token_ws (by decide) hw hb) hel he

/--
An object can still be read after some leading whitespace has been skipped. It is the object's
counterpart to the array case, needed separately because `Object` is a distinct production with
its own two constructors.

`hw : Ws x y` and `h : Object x f r` give `Object y f r`, the same fields and the same remainder.
Both `empty` and `members` open with a `BeginObject`, moved by `token_ws` with `decide` supplying
that `'{'` is not whitespace.
-/
theorem obj_ws {x y : List Char} {f : Array (String × Json)} {r : List Char} (hw : Ws x y)
    (h : Object x f r) : Object y f r := by
  cases h with
  | empty hb he => exact Object.empty (token_ws (by decide) hw hb) he
  | members hb hms he => exact Object.members (token_ws (by decide) hw hb) hms he

/--
A value can still be read after some leading whitespace has been skipped. This is the form the
uniqueness proof uses when it brings two derivations to a common starting point, and it has to
hold for all seven alternatives rather than only the two containers.

`hw : Ws x y` and `h : Value x j r` give `Value y j r`, the same value and remainder. The
literals, strings and numbers begin with a character that is not whitespace, so
`ws_eq_of_not_isWs` says nothing was taken and `y` is `x` itself; for a number that character is a
minus or a digit, and `isWs_of_isDigit` is what settles the digit case. Only the containers
actually absorb whitespace, and they do so through `arr_ws` and `obj_ws`.
-/
theorem value_ws {x y : List Char} {j : Json} {r : List Char} (hw : Ws x y)
    (h : Value x j r) : Value y j r := by
  cases h with
  | false_ => rw [ws_eq_of_not_isWs (by decide) hw]; exact Value.false_
  | null => rw [ws_eq_of_not_isWs (by decide) hw]; exact Value.null
  | true_ => rw [ws_eq_of_not_isWs (by decide) hw]; exact Value.true_
  | str hs =>
    cases hs with
    | mk hcs => rw [ws_eq_of_not_isWs (by decide) hw]; exact Value.str (Str.mk hcs)
  | num hn =>
    obtain ⟨c, t, hct, hc⟩ := num_head hn
    subst hct
    have : isWs c = false := by
      rcases hc with rfl | hd
      · decide
      · exact isWs_of_isDigit hd
    rw [ws_eq_of_not_isWs this hw]
    exact Value.num hn
  | arr ha => exact Value.arr (arr_ws hw ha)
  | obj ho => exact Value.obj (obj_ws hw ho)

/--
A list of array elements can still be read after some leading whitespace has been skipped. Its
first element is a value, so this is `value_ws` carried through the two constructors of
`Elements`.

`hw : Ws x y` and `h : Elements x vs r` give `Elements y vs r`, the same values and remainder.
Both `one` and `more` open with a `Value`, which `value_ws` moves; the separator and the tail of
the list are untouched, being reached only after that first value.
-/
theorem elements_ws {x y : List Char} {vs : List Json} {r : List Char} (hw : Ws x y)
    (h : Elements x vs r) : Elements y vs r := by
  cases h with
  | one hv => exact Elements.one (value_ws hw hv)
  | more hv hs he => exact Elements.more (value_ws hw hv) hs he

/--
An object member can still be read after some leading whitespace has been skipped, and in fact
none can have been. A member opens with a string literal, whose quotation mark is not whitespace,
so the run must have consumed nothing.

`hw : Ws x y` and `h : Member x m r` give `Member y m r`. The single constructor opens with a
`Str`, which begins with `'"'`, so `ws_eq_of_not_isWs` says `y` is `x` and the derivation is
rebuilt exactly as it was. The colon and the value that follow are carried across unchanged.
-/
theorem member_ws {x y : List Char} {m : String × Json} {r : List Char} (hw : Ws x y)
    (h : Member x m r) : Member y m r := by
  cases h with
  | mk hstr hsep hval =>
    cases hstr with
    | mk hcs =>
      rw [ws_eq_of_not_isWs (by decide) hw]
      exact Member.mk (Str.mk hcs) hsep hval

/--
A list of object members can still be read after some leading whitespace has been skipped. It is
the object counterpart of the claim about elements, and is used in the same place: bringing two
derivations of one text to a common starting point.

`hw : Ws x y` and `h : Members x ms r` give `Members y ms r`, the same fields and remainder. Both
`one` and `more` open with a `Member`, which `member_ws` moves; as there, the run turns out to
have consumed nothing.
-/
theorem members_ws {x y : List Char} {ms : List (String × Json)} {r : List Char}
    (hw : Ws x y) (h : Members x ms r) : Members y ms r := by
  cases h with
  | one hm => exact Members.one (member_ws hw hm)
  | more hm hs hms => exact Members.more (member_ws hw hm) hs hms


/-! ## The value family

`Value`, `Arr`, `Object`, `Elements`, `Members` and `Member` are one mutual definition, which the
`induction` tactic will not take apart. It does not have to: every derivation leaves less text
than it was given, so an induction on the length of the text carries all six, and within one
length they are proved in the order they depend on one another.

Each statement carries what pins its remainder down. A value needs only `Follows`, since what
can come after one is the end of the text or a separator or a closing bracket. A run of elements
or members needs the closing bracket itself, because `1` followed by `,2]` and `1,2` followed by
`]` are both derivations of the same text, and only the bracket tells them apart.
-/

/--
Two texts differing only by whitespace can both be advanced to a single text. `WsEq` is a
disjunction that says nothing about which of the two is further on, and this turns it into a
common point that a proof can work forward from without case-splitting again.

`h : WsEq a b` is `Ws a b ∨ Ws b a`. The conclusion produces a `c` with `Ws a c` and `Ws b c`,
so both texts reach it by whitespace. In each disjunct `c` is whichever of the two is already the
further on, the other run being `Ws.nil`; no text beyond those two is ever needed.
-/
private theorem wsEq_common {a b : List Char} (h : WsEq a b) : ∃ c, Ws a c ∧ Ws b c := by
  rcases h with hab | hba
  · exact ⟨b, hab, Ws.nil⟩
  · exact ⟨a, Ws.nil, hba⟩

/--
A run of whitespace reaching a character that is not whitespace reaches it from either of two
starting points that differ only by whitespace. It is what carries a structural character's
position from one of two derivations being compared to the other.

`h : WsEq a b` relates the two starting points, `hws : Ws a (t :: u)` is the run from the first,
and `hnw` says `t` is not whitespace. The conclusion `Ws b (t :: u)` runs from the second to the
same place. Where `b` is behind `a` the two runs simply compose; where it is ahead, confluence
together with `ws_eq_of_not_isWs` shows it cannot have gone past `t`, and `hnw` is what forbids
that.
-/
private theorem ws_to_token {a b : List Char} {t : Char} {u : List Char} (h : WsEq a b)
    (hws : Ws a (t :: u)) (hnw : isWs t = false) : Ws b (t :: u) := by
  rcases h with hab | hba
  · rcases hab.confluent hws with hc | hc
    · exact hc
    · rw [ws_eq_of_not_isWs hnw hc]
      exact Ws.nil
  · exact hba.trans hws

private def ArrUnique (s : List Char) : Prop :=
  ∀ {e₁ r₁ e₂ r₂}, Arr s e₁ r₁ → Arr s e₂ r₂ → e₁ = e₂ ∧ WsEq r₁ r₂

private def ObjectUnique (s : List Char) : Prop :=
  ∀ {f₁ r₁ f₂ r₂}, Object s f₁ r₁ → Object s f₂ r₂ → f₁ = f₂ ∧ WsEq r₁ r₂

private def ValueUnique (s : List Char) : Prop :=
  ∀ {j₁ r₁ j₂ r₂}, Value s j₁ r₁ → Value s j₂ r₂ → Follows r₁ → Follows r₂ →
    j₁ = j₂ ∧ WsEq r₁ r₂

private def ElementsUnique (s : List Char) : Prop :=
  ∀ {vs₁ r₁ vs₂ r₂ x₁ x₂}, Elements s vs₁ r₁ → Elements s vs₂ r₂ →
    EndArray r₁ x₁ → EndArray r₂ x₂ → vs₁ = vs₂ ∧ WsEq r₁ r₂

private def MemberUnique (s : List Char) : Prop :=
  ∀ {m₁ r₁ m₂ r₂}, Member s m₁ r₁ → Member s m₂ r₂ → Follows r₁ → Follows r₂ →
    m₁ = m₂ ∧ WsEq r₁ r₂

private def MembersUnique (s : List Char) : Prop :=
  ∀ {ms₁ r₁ ms₂ r₂ x₁ x₂}, Members s ms₁ r₁ → Members s ms₂ r₂ →
    EndObject r₁ x₁ → EndObject r₂ x₂ → ms₁ = ms₂ ∧ WsEq r₁ r₂

/--
Each of the six mutually recursive productions names at most one value for a text, given whatever
pins its remainder down. They are one mutual definition, so none can be proved alone; this proves
all six together, and `text_unique` is what the rest of the library takes from it.

`n` bounds the text's length, by `hs : s.length ≤ n`, and the induction runs on `n`, every
derivation leaving strictly less text by the bounds in `Json.Spec.Length`. Each conjunct is one of
the six `…Unique` predicates: two derivations from the same `s` agree on the value they name,
and their remainders are `WsEq`, which is as much as can be claimed, whitespace being divisible
anywhere. `ValueUnique` and `MemberUnique` carry `Follows` on both remainders; `ElementsUnique`
and `MembersUnique` carry the closing bracket or brace instead, since `1` followed by `,2]` and
`1,2` followed by `]` derive the same text and only that bracket tells them apart; `ArrUnique` and
`ObjectUnique` need no condition, their own brackets ending them. The bound cannot empty the
claim, `n := s.length` satisfying `hs` for every `s`.
-/
private theorem family_unique : ∀ (n : Nat) (s : List Char), s.length ≤ n →
    ArrUnique s ∧ ObjectUnique s ∧ ValueUnique s ∧ ElementsUnique s ∧ MemberUnique s ∧
      MembersUnique s := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs
    have harr : ArrUnique s := by
      intro e₁ r₁ e₂ r₂ h₁ h₂
      cases h₁ with
      | empty hb₁ he₁ =>
        cases h₂ with
        | empty hb₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₁'.confluent w₂'
          obtain ⟨v₁, v₁'⟩ := he₁
          obtain ⟨v₂, v₂'⟩ := he₂
          obtain ⟨-, hv⟩ := wsEq_token_eq hae v₁ v₂ (by decide) (by decide)
          subst hv
          exact ⟨rfl, v₁'.confluent v₂'⟩
        | items hb₂ hel₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₁'.confluent w₂'
          obtain ⟨v₁, -⟩ := he₁
          exact absurd (elements_ws (ws_to_token hae v₁ (by decide)) hel₂) not_elements_bracket
      | items hb₁ hel₁ he₁ =>
        cases h₂ with
        | empty hb₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₂'.confluent w₁'
          obtain ⟨v₂, -⟩ := he₂
          exact absurd (elements_ws (ws_to_token hae v₂ (by decide)) hel₁) not_elements_bracket
        | items hb₂ hel₂ he₂ =>
          have hlen := token_length hb₁
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hvs, hbe⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.2.1 (elements_ws hc₁ hel₁)
              (elements_ws hc₂ hel₂) he₁ he₂
          obtain ⟨v₁, v₁'⟩ := he₁
          obtain ⟨v₂, v₂'⟩ := he₂
          obtain ⟨-, hv⟩ := wsEq_token_eq hbe v₁ v₂ (by decide) (by decide)
          subst hv
          exact ⟨by rw [hvs], v₁'.confluent v₂'⟩
    have hobj : ObjectUnique s := by
      intro f₁ r₁ f₂ r₂ h₁ h₂
      cases h₁ with
      | empty hb₁ he₁ =>
        cases h₂ with
        | empty hb₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₁'.confluent w₂'
          obtain ⟨v₁, v₁'⟩ := he₁
          obtain ⟨v₂, v₂'⟩ := he₂
          obtain ⟨-, hv⟩ := wsEq_token_eq hae v₁ v₂ (by decide) (by decide)
          subst hv
          exact ⟨rfl, v₁'.confluent v₂'⟩
        | members hb₂ hms₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₁'.confluent w₂'
          obtain ⟨v₁, -⟩ := he₁
          exact absurd (members_ws (ws_to_token hae v₁ (by decide)) hms₂) not_members_brace
      | members hb₁ hms₁ he₁ =>
        cases h₂ with
        | empty hb₂ he₂ =>
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          have hae : WsEq _ _ := w₂'.confluent w₁'
          obtain ⟨v₂, -⟩ := he₂
          exact absurd (members_ws (ws_to_token hae v₂ (by decide)) hms₁) not_members_brace
        | members hb₂ hms₂ he₂ =>
          have hlen := token_length hb₁
          obtain ⟨w₁, w₁'⟩ := hb₁
          obtain ⟨w₂, w₂'⟩ := hb₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hms, hbe⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.2.2.2 (members_ws hc₁ hms₁)
              (members_ws hc₂ hms₂) he₁ he₂
          obtain ⟨v₁, v₁'⟩ := he₁
          obtain ⟨v₂, v₂'⟩ := he₂
          obtain ⟨-, hv⟩ := wsEq_token_eq hbe v₁ v₂ (by decide) (by decide)
          subst hv
          exact ⟨by rw [hms], v₁'.confluent v₂'⟩
    have hval : ValueUnique s := by
      intro j₁ r₁ j₂ r₂ h₁ h₂ f₁ f₂
      cases h₁ with
      | false_ =>
        cases h₂ with
        | false_ => exact ⟨rfl, WsEq.refl _⟩
        | str hst => exact absurd hst (not_str_cons (by decide))
        | num hn => exact absurd hn (not_num_cons (by decide) (by decide))
        | arr ha => exact absurd ha (not_arr_cons (by decide) (by decide))
        | obj ho => exact absurd ho (not_obj_cons (by decide) (by decide))
      | null =>
        cases h₂ with
        | null => exact ⟨rfl, WsEq.refl _⟩
        | str hst => exact absurd hst (not_str_cons (by decide))
        | num hn => exact absurd hn (not_num_cons (by decide) (by decide))
        | arr ha => exact absurd ha (not_arr_cons (by decide) (by decide))
        | obj ho => exact absurd ho (not_obj_cons (by decide) (by decide))
      | true_ =>
        cases h₂ with
        | true_ => exact ⟨rfl, WsEq.refl _⟩
        | str hst => exact absurd hst (not_str_cons (by decide))
        | num hn => exact absurd hn (not_num_cons (by decide) (by decide))
        | arr ha => exact absurd ha (not_arr_cons (by decide) (by decide))
        | obj ho => exact absurd ho (not_obj_cons (by decide) (by decide))
      | str hs₁ =>
        obtain ⟨t, hshape⟩ := str_head hs₁
        subst hshape
        cases h₂ with
        | str hs₂ =>
          obtain ⟨hv, hr⟩ := str_unique hs₁ hs₂
          exact ⟨by rw [hv], by rw [hr]; exact WsEq.refl _⟩
        | num hn => exact absurd hn (not_num_cons (by decide) (by decide))
        | arr ha => exact absurd ha (not_arr_cons (by decide) (by decide))
        | obj ho => exact absurd ho (not_obj_cons (by decide) (by decide))
      | num hn₁ =>
        cases h₂ with
        | false_ => exact absurd hn₁ (not_num_cons (by decide) (by decide))
        | null => exact absurd hn₁ (not_num_cons (by decide) (by decide))
        | true_ => exact absurd hn₁ (not_num_cons (by decide) (by decide))
        | str hst =>
          obtain ⟨t, hshape⟩ := str_head hst
          subst hshape
          exact absurd hn₁ (not_num_cons (by decide) (by decide))
        | num hn₂ =>
          obtain ⟨hv, hr⟩ := num_unique hn₁ hn₂ f₁ f₂
          exact ⟨by rw [hv], by rw [hr]; exact WsEq.refl _⟩
        | arr ha =>
          obtain ⟨c, t, hct, hc⟩ := num_head hn₁
          subst hct
          rcases hc with rfl | hd
          · exact absurd ha (not_arr_cons (by decide) (by decide))
          · exact absurd ha (not_arr_cons (isWs_of_isDigit hd) (digit_ne hd (by decide)))
        | obj ho =>
          obtain ⟨c, t, hct, hc⟩ := num_head hn₁
          subst hct
          rcases hc with rfl | hd
          · exact absurd ho (not_obj_cons (by decide) (by decide))
          · exact absurd ho (not_obj_cons (isWs_of_isDigit hd) (digit_ne hd (by decide)))
      | arr ha₁ =>
        cases h₂ with
        | false_ => exact absurd ha₁ (not_arr_cons (by decide) (by decide))
        | null => exact absurd ha₁ (not_arr_cons (by decide) (by decide))
        | true_ => exact absurd ha₁ (not_arr_cons (by decide) (by decide))
        | str hst =>
          obtain ⟨t, hshape⟩ := str_head hst
          subst hshape
          exact absurd ha₁ (not_arr_cons (by decide) (by decide))
        | num hn =>
          obtain ⟨c, t, hct, hc⟩ := num_head hn
          subst hct
          rcases hc with rfl | hd
          · exact absurd ha₁ (not_arr_cons (by decide) (by decide))
          · exact absurd ha₁ (not_arr_cons (isWs_of_isDigit hd) (digit_ne hd (by decide)))
        | arr ha₂ =>
          obtain ⟨he, hr⟩ := harr ha₁ ha₂
          exact ⟨by rw [he], hr⟩
        | obj ho =>
          obtain ⟨u₁, w₁⟩ := arr_begin ha₁
          obtain ⟨u₂, w₂⟩ := obj_begin ho
          obtain ⟨hc, -⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
      | obj ho₁ =>
        cases h₂ with
        | false_ => exact absurd ho₁ (not_obj_cons (by decide) (by decide))
        | null => exact absurd ho₁ (not_obj_cons (by decide) (by decide))
        | true_ => exact absurd ho₁ (not_obj_cons (by decide) (by decide))
        | str hst =>
          obtain ⟨t, hshape⟩ := str_head hst
          subst hshape
          exact absurd ho₁ (not_obj_cons (by decide) (by decide))
        | num hn =>
          obtain ⟨c, t, hct, hc⟩ := num_head hn
          subst hct
          rcases hc with rfl | hd
          · exact absurd ho₁ (not_obj_cons (by decide) (by decide))
          · exact absurd ho₁ (not_obj_cons (isWs_of_isDigit hd) (digit_ne hd (by decide)))
        | arr ha =>
          obtain ⟨u₁, w₁⟩ := obj_begin ho₁
          obtain ⟨u₂, w₂⟩ := arr_begin ha
          obtain ⟨hc, -⟩ := wsEq_token_eq (WsEq.refl s) w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
        | obj ho₂ =>
          obtain ⟨hf, hr⟩ := hobj ho₁ ho₂
          exact ⟨by rw [hf], hr⟩
    have hels : ElementsUnique s := by
      intro vs₁ r₁ vs₂ r₂ x₁ x₂ h₁ h₂ e₁ e₂
      cases h₁ with
      | one hv₁ =>
        cases h₂ with
        | one hv₂ =>
          obtain ⟨hv, hr⟩ :=
            hval hv₁ hv₂ (follows_of_token e₁ (by decide)) (follows_of_token e₂ (by decide))
          exact ⟨by rw [hv], hr⟩
        | more hv₂ hsep₂ _ =>
          obtain ⟨-, hwe⟩ :=
            hval hv₁ hv₂ (follows_of_token e₁ (by decide)) (follows_of_token hsep₂ (by decide))
          obtain ⟨w₁, -⟩ := e₁
          obtain ⟨w₂, -⟩ := hsep₂
          obtain ⟨hc, -⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
      | more hv₁ hsep₁ hel₁ =>
        cases h₂ with
        | one hv₂ =>
          obtain ⟨-, hwe⟩ :=
            hval hv₁ hv₂ (follows_of_token hsep₁ (by decide)) (follows_of_token e₂ (by decide))
          obtain ⟨w₁, -⟩ := hsep₁
          obtain ⟨w₂, -⟩ := e₂
          obtain ⟨hc, -⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
        | more hv₂ hsep₂ hel₂ =>
          obtain ⟨hveq, hwe⟩ :=
            hval hv₁ hv₂ (follows_of_token hsep₁ (by decide)) (follows_of_token hsep₂ (by decide))
          have hlen₁ := value_length hv₁
          have hlen₂ := token_length hsep₁
          obtain ⟨w₁, w₁'⟩ := hsep₁
          obtain ⟨w₂, w₂'⟩ := hsep₂
          obtain ⟨-, hu⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hvs, hr⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.2.1 (elements_ws hc₁ hel₁)
              (elements_ws hc₂ hel₂) e₁ e₂
          exact ⟨by rw [hveq, hvs], hr⟩
    have hmem : MemberUnique s := by
      intro m₁ r₁ m₂ r₂ h₁ h₂ f₁ f₂
      cases h₁ with
      | mk hs₁ hn₁ hv₁ =>
        cases h₂ with
        | mk hs₂ hn₂ hv₂ =>
          have hlen₁ := str_length hs₁
          have hlen₂ := token_length hn₁
          obtain ⟨hk, ha⟩ := str_unique hs₁ hs₂
          subst ha
          obtain ⟨w₁, w₁'⟩ := hn₁
          obtain ⟨w₂, w₂'⟩ := hn₂
          obtain ⟨-, hu⟩ := wsEq_token_eq (WsEq.refl _) w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hv, hr⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.1 (value_ws hc₁ hv₁) (value_ws hc₂ hv₂) f₁ f₂
          exact ⟨by rw [hk, hv], hr⟩
    have hmems : MembersUnique s := by
      intro ms₁ r₁ ms₂ r₂ x₁ x₂ h₁ h₂ e₁ e₂
      cases h₁ with
      | one hm₁ =>
        cases h₂ with
        | one hm₂ =>
          obtain ⟨hm, hr⟩ :=
            hmem hm₁ hm₂ (follows_of_token e₁ (by decide)) (follows_of_token e₂ (by decide))
          exact ⟨by rw [hm], hr⟩
        | more hm₂ hsep₂ _ =>
          obtain ⟨-, hwe⟩ :=
            hmem hm₁ hm₂ (follows_of_token e₁ (by decide)) (follows_of_token hsep₂ (by decide))
          obtain ⟨w₁, -⟩ := e₁
          obtain ⟨w₂, -⟩ := hsep₂
          obtain ⟨hc, -⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
      | more hm₁ hsep₁ hms₁ =>
        cases h₂ with
        | one hm₂ =>
          obtain ⟨-, hwe⟩ :=
            hmem hm₁ hm₂ (follows_of_token hsep₁ (by decide)) (follows_of_token e₂ (by decide))
          obtain ⟨w₁, -⟩ := hsep₁
          obtain ⟨w₂, -⟩ := e₂
          obtain ⟨hc, -⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          exact absurd hc (by decide)
        | more hm₂ hsep₂ hms₂ =>
          obtain ⟨hmeq, hwe⟩ :=
            hmem hm₁ hm₂ (follows_of_token hsep₁ (by decide)) (follows_of_token hsep₂ (by decide))
          have hlen₁ := member_length hm₁
          have hlen₂ := token_length hsep₁
          obtain ⟨w₁, w₁'⟩ := hsep₁
          obtain ⟨w₂, w₂'⟩ := hsep₂
          obtain ⟨-, hu⟩ := wsEq_token_eq hwe w₁ w₂ (by decide) (by decide)
          subst hu
          obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (w₁'.confluent w₂')
          have hcl : c.length < n := by
            have := Ws.length_le hc₁
            omega
          obtain ⟨hms, hr⟩ :=
            (ih c.length hcl c (Nat.le_refl _)).2.2.2.2.2 (members_ws hc₁ hms₁)
              (members_ws hc₂ hms₂) e₁ e₂
          exact ⟨by rw [hmeq, hms], hr⟩
    exact ⟨harr, hobj, hval, hels, hmem, hmems⟩


/-! ## Text -/

/--
A text names at most one value. This is a claim about the transcription of the grammar rather than
about the parser: were two values derivable from one text, "the value this text denotes" would
mean nothing, and no proof about the parser could repair it.

`h₁ : Text s j₁` and `h₂ : Text s j₂` each say `s` is whitespace, then a value, then
whitespace, with nothing left over. The conclusion `j₁ = j₂` equates the two values; the
remainders are not compared, `Text` having already required both to be empty. The two derivations
need not divide the leading whitespace the same way, so `wsEq_common` and `value_ws` bring them to
a common starting point first, and `follows_of_ws` then supplies `Follows` for both remainders, a
text ending in nothing but whitespace.
-/
theorem text_unique {s : List Char} {j₁ j₂ : Json} (h₁ : Text s j₁) (h₂ : Text s j₂) : j₁ = j₂ := by
  obtain ⟨a₁, b₁, hw₁, hv₁, he₁⟩ := h₁
  obtain ⟨a₂, b₂, hw₂, hv₂, he₂⟩ := h₂
  obtain ⟨c, hc₁, hc₂⟩ := wsEq_common (hw₁.confluent hw₂)
  exact ((family_unique c.length c (Nat.le_refl _)).2.2.1 (value_ws hc₁ hv₁) (value_ws hc₂ hv₂)
    (follows_of_ws he₁) (follows_of_ws he₂)).1

/--
A `String` names at most one value. `parse` takes a `String` rather than a list of characters, so
this is the form of uniqueness that the parser's own theorems can be composed with.

`TextOf s j` is `Text s.toList j`, so the two hypotheses are `Text` derivations over the string's
characters and the conclusion `j₁ = j₂` is `text_unique` applied to that list. The conversion
is definitional, so nothing is proved here beyond restating the claim at the type the entry point
uses.
-/
theorem textOf_unique {s : String} {j₁ j₂ : Json} (h₁ : TextOf s j₁) (h₂ : TextOf s j₂) :
    j₁ = j₂ := text_unique h₁ h₂

end Json.Spec
