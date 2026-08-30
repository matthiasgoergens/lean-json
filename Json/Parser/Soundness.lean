/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser
public import Json.Spec
public import Json.Spec.Unambiguity
public import Json.Spec.Canonical

public section

namespace Json.Parser

/-!
What the parser accepts, stated against the grammar.

The scanner walks the text by position, while `Json.Spec` is written over a list of characters, so
the two are related here first: `remaining p` is what is left of the text at `p`, and one step of
the scanner takes one character off the front of it. Everything else is proved in those terms.

The leaves come first: whitespace, the literals, the parts of a number, and a string with its
escapes. The machine follows, where what a stack of frames still demands of the text is written
down as `Closes` and every accepting run is shown to have a derivation behind it.
-/

section
variable {s : String}

/-- What is left of the text at `p`. -/
def remaining (p : s.Pos) : List Char := (s.sliceFrom p).copy.toList

/--
At the beginning of the text nothing has been read. The scanner walks a position while the grammar
is written over a list of characters, and this is where the two are anchored: the whole text is
what remains at the start.

`remaining s.startPos = s.toList` says the text left at the initial position is the string's own
characters. It is the base case of every claim relating a parse to a derivation, since every entry
point begins there or one character past a byte order mark.
-/
theorem remaining_startPos : remaining s.startPos = s.toList := by
  rw [remaining, String.Pos.Splits.eq_right s.startPos.splits (String.splits_startPos s)]

/--
At the end of the text nothing is left. It is what turns the scanner running out of characters
into the empty remainder the grammar's `Text` production demands.

`remaining s.endPos = []` says the text left at the final position is empty. Together with the
claim about the start it fixes the two ends of the correspondence; what happens in between is the
step below.
-/
theorem remaining_endPos : remaining s.endPos = [] := by
  rw [remaining, String.Pos.Splits.eq_right s.endPos.splits (String.splits_endPos s)]
  rfl

/--
Reading one character takes that character off the front of what remains. This is the whole of the
correspondence between the scanner's positions and the grammar's lists: every soundness claim in
the module is some derivation built by repeating it.

`h : step? p = some (c, q)` says `c` is the character at `p` and `q` the position after it. The
conclusion `remaining p = c :: remaining q` puts `c` at the head of what remained at `p`, with the
rest being what remains at `q`. The `none` case of `step?` cannot arise under `h`, which is what
makes the list a `cons` rather than possibly empty.
-/
theorem remaining_step {p q : s.Pos} {c : Char} (h : step? p = some (c, q)) :
    remaining p = c :: remaining q := by
  rw [step?] at h
  split at h
  · simp at h
  · next hp =>
    obtain ⟨hc, hq⟩ := Prod.mk.injEq .. ▸ Option.some.injEq .. ▸ h
    subst hc
    subst hq
    rw [remaining, String.Pos.Splits.eq_right p.splits (String.Pos.splits_next_right p hp),
      remaining]
    simp

/--
Where the scanner finds no character, nothing remains. It is what a parse must establish at the
end of a document in order for the trailing whitespace to consume everything.

`h : step? p = none` says `p` is the end of the text, that being the only way `step?` fails. The
conclusion `remaining p = []` is then `remaining_endPos` at that position.
-/
theorem remaining_none {p : s.Pos} (h : step? p = none) : remaining p = [] := by
  rw [step?] at h
  split at h
  · next hp => exact hp ▸ remaining_endPos
  · simp at h


/-! ## Whitespace and literals -/

/--
Whatever the whitespace skipper passes over is whitespace in the grammar's sense. `ws` surrounds
every structural character, so this is used at nearly every step of the machine, and it is what
lets a scanner that consumes greedily be matched against a relation that may stop anywhere.

The conclusion is a `Ws` derivation taking the text at `start` to the text at the position the
skipper stopped at. The proof follows `skipWs.go`, whose three cases are a whitespace character
consumed, a non-whitespace character reached, and the end of the text; the last two are `Ws.nil`,
so a skipper that consumes nothing is still a derivation.
-/
theorem ws_skipWs (start : s.Pos) :
    Spec.Ws (remaining start) (remaining (skipWs start).pos) := by
  have go : ∀ (p : s.Pos) (h : p.remainingBytes ≤ start.remainingBytes),
      Spec.Ws (remaining p) (remaining (skipWs.go start p h).pos) := by
    intro p h
    fun_induction skipWs.go start p h with
    | case1 p h c q hc hws ih =>
      rw [remaining_step hc]
      exact Spec.Ws.cons hws ih
    | case2 p h c q hc hws => exact Spec.Ws.nil
    | case3 p h hc => exact Spec.Ws.nil
  exact go start (Nat.le_refl _)

/--
Where the scanner matches a fixed list of characters, those characters are what it consumed. The
literals `null`, `true` and `false` are read this way, so their derivations depend on knowing
exactly which characters were taken.

`h : expect? p l = some r` says the text at `p` begins with `l` and `r.pos` is the position after
it. `remaining p = l ++ remaining r.pos` splits the remainder at that boundary. The induction is
on `l`, generalising `p` and `r`, since each character is matched at a fresh position.
-/
theorem expect?_eq {p : s.Pos} {l : List Char} {r : Consumed Unit p} (h : expect? p l = some r) :
    remaining p = l ++ remaining r.pos := by
  induction l generalizing p r with
  | nil =>
    rw [expect?] at h
    injection h with h
    simp [← h]
  | cons c rest ih =>
    rw [expect?] at h
    split at h
    · next c' q hc =>
      split at h
      · next hcc =>
        split at h
        · next t ht =>
          injection h with h
          rw [remaining_step hc, ← h, ih ht]
          simp [eq_of_beq hcc]
        · simp at h
      · simp at h
    · simp at h


/-! ## Numbers

The scanner reads digits left to right, accumulating as it goes, while `Spec.Digits` is built from
the first digit and the run that follows it. What bridges them is the invariant below: a run
either stops where it started or forms a `Digits` derivation whose value and length combine with
what the loop had already accumulated.
-/

/--
A run of digits either consumed nothing or forms a `Digits` derivation whose value and length
combine with what the loop had already accumulated. The scanner reads digits left to right into an
accumulator while `Spec.Digits` is built from the first digit and the run after it, so the two can
only be compared through an invariant that holds part way through.

`p`, `value` and `count` are the loop's state and `h` its bookkeeping bound. The conclusion is a
disjunction: either the loop stopped where it started, leaving its state untouched, or there are a
`v` and an `n` such that the text consumed is a `Digits` derivation of `v` with `n` digits and the
loop's state has become `(value * 10 ^ n + v, count + n)`. The first disjunct is what covers a
position where no digit is found, which is not a failure but an empty run.
-/
private theorem digits_go_sound {start : s.Pos} :
    ∀ (p : s.Pos) (value count : Nat) (h : p.remainingBytes ≤ start.remainingBytes),
      ((digits.go start p value count h).pos = p ∧
          (digits.go start p value count h).value = (value, count)) ∨
        ∃ v n, Spec.Digits (remaining p) v n (remaining (digits.go start p value count h).pos) ∧
          (digits.go start p value count h).value = (value * 10 ^ n + v, count + n) := by
  intro p value count h
  fun_induction digits.go start p value count h with
  | case1 p value count h c q hc hd ih =>
    refine .inr ?_
    rcases ih with ⟨hpos, hval⟩ | ⟨v, n, hspec, hval⟩
    · refine ⟨Spec.digitVal c, 1, ?_, by rw [hval]⟩
      rw [remaining_step hc, hpos]
      exact Spec.Digits.last hd
    · refine ⟨Spec.digitVal c * 10 ^ n + v, n + 1, ?_, ?_⟩
      · rw [remaining_step hc]
        exact Spec.Digits.cons hd hspec
      · rw [hval, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ n)]
        simp only [Prod.mk.injEq]
        omega
  | case2 p value count h c q hc hd => exact .inl ⟨rfl, rfl⟩
  | case3 p value count h hc => exact .inl ⟨rfl, rfl⟩

/--
A digit followed by the run of digits after it is a `Digits` derivation. The grammar requires at
least one digit, so the scanner's possibly-empty loop has to be preceded by a character read
separately, and this is where the two are put together.

`hc` says `c` is the character at `p` and `hd` says it is a digit. The conclusion is a `Digits`
derivation from `remaining p` recording the value and the count the loop returns, and leaving what
remains at the loop's stopping position. The two cases of `digits_go_sound` become `Digits.last`,
where the run after `c` was empty, and `Digits.cons`, where it was not.
-/
theorem digits_sound {p q : s.Pos} {c : Char} (hc : step? p = some (c, q))
    (hd : Spec.isDigit c = true) :
    Spec.Digits (remaining p) (digits q (Spec.digitVal c) 1).value.1
      (digits q (Spec.digitVal c) 1).value.2 (remaining (digits q (Spec.digitVal c) 1).pos) := by
  rw [digits, remaining_step hc]
  rcases digits_go_sound (start := q) q (Spec.digitVal c) 1 (Nat.le_refl _) with
    ⟨hpos, hval⟩ | ⟨v, n, hspec, hval⟩
  · rw [hpos, hval]
    exact Spec.Digits.last hd
  · rw [hval, Nat.add_comm 1 n]
    exact Spec.Digits.cons hd hspec


/--
A digit that is not `'0'` lies between `'1'` and `'9'`. The grammar's `int` production splits on
exactly that, and the scanner splits on whether the character is `'0'`, so the two conditions have
to be reconciled.

`hd : Spec.isDigit c = true` and `h0 : ¬ c = '0'` are the scanner's two facts. The conclusion is
the side condition `Int'.digits` asks for. It is arithmetic on the code points: `isDigit` puts `c`
between 48 and 57, and `h0` removes 48, which leaves the range starting at 49.
-/
private theorem one_le_of_isDigit {c : Char} (hd : Spec.isDigit c = true) (h0 : ¬ c = '0') :
    ('1' ≤ c && c ≤ '9') = true := by
  simp only [Spec.isDigit, Bool.and_eq_true, decide_eq_true_eq, Char.le_def,
    UInt32.le_iff_toNat_le] at hd ⊢
  obtain ⟨hd1, hd2⟩ := hd
  have hne : c.val.toNat ≠ ('0' : Char).val.toNat := fun he => h0 (Char.toNat_inj.mp he)
  have h0' : ('0' : Char).val.toNat = 48 := rfl
  have h1' : ('1' : Char).val.toNat = 49 := rfl
  omega

/--
What the scanner accepts as an integer part is an `int` of the grammar, denoting the value it
returns. It is the first of the number parts, and the only one that must consume something.

`h : intPart p = .ok r` says the scan succeeded with the result `r`. The `Spec.Int'` derivation
runs from the text at `p`, records `r.value.1`, the value the scanner computed, and leaves what
remains where it stopped; `r.value.2`, the digit count, is not part of `Int'` and is dropped. The
`'0'` branch is `Int'.zero`, and the other is `Int'.digits` with `one_le_of_isDigit` supplying its
side condition.
-/
theorem intPart_sound {p : s.Pos} {r : Scanned (Nat × Nat) p} (h : intPart p = .ok r) :
    Spec.Int' (remaining p) r.value.1 (remaining r.pos) := by
  rw [intPart] at h
  split at h
  · next q hc =>
    injection h with h
    rw [remaining_step hc, ← h]
    exact Spec.Int'.zero
  · next c q hne hc =>
    split at h
    · next hd =>
      injection h with h
      have hdig := digits_sound hc hd
      rw [remaining_step hc] at hdig
      rw [remaining_step hc, ← h]
      exact Spec.Int'.digits (one_le_of_isDigit hd hne) hdig
    · simp at h
  · simp at h


/--
What the scanner accepts as a fraction is a `frac` of the grammar, denoting the value and the
digit count it returns. The fraction is optional, so the scan that consumes nothing has to be a
derivation too.

`h : fracPart p = .ok r` says the scan succeeded. The `Spec.Frac` derivation runs from the text at
`p` and records both `r.value.1`, the value, and `r.value.2`, the number of digits, the latter
mattering because the exponent is adjusted by it. Where the text does not begin with `'.'` the
scanner returns `(0, 0)` at the same position, which is `Frac.absent`.
-/
theorem fracPart_sound {p : s.Pos} {r : Consumed (Nat × Nat) p} (h : fracPart p = .ok r) :
    Spec.Frac (remaining p) r.value.1 r.value.2 (remaining r.pos) := by
  rw [fracPart] at h
  split at h
  · next q hc =>
    split at h
    · next c t hd =>
      split at h
      · next hdig =>
        injection h with h
        have hdigs := digits_sound hd hdig
        rw [remaining_step hc, ← h]
        exact Spec.Frac.present hdigs
      · simp at h
    · simp at h
  · injection h with h
    rw [← h]
    exact Spec.Frac.absent

/--
The optional sign of an exponent is a plus, a minus, or nothing, and the scanner's flag says
which. Reading an exponent back means knowing exactly what the sign did, since it is what decides
the exponent's sign.

The conclusion is a three-way disjunction, one case per branch of `expSign`: no sign, with the
position unmoved and the flag `false`; a `'+'` consumed with the flag still `false`; and a `'-'`
consumed with the flag `true`. Each case that consumes states the character taken through
`remaining_step`, which is what `Exp.plus` and `Exp.minus` need.
-/
private theorem expSign_sound (p : s.Pos) :
    ((expSign p).value = false ∧ (expSign p).pos = p) ∨
      ((expSign p).value = false ∧ remaining p = '+' :: remaining (expSign p).pos) ∨
      ((expSign p).value = true ∧ remaining p = '-' :: remaining (expSign p).pos) := by
  rw [expSign]
  split
  · next q hs => exact .inr (.inl ⟨rfl, remaining_step hs⟩)
  · next q hs => exact .inr (.inr ⟨rfl, remaining_step hs⟩)
  · exact .inl ⟨rfl, rfl⟩

/--
What the scanner accepts as an exponent is an `exp` of the grammar, denoting the value it returns.
It is optional and has three present forms, so this is the widest of the number parts.

`h : expPart p = .ok r` says the scan succeeded. The `Spec.Exp` derivation runs from the text at
`p` and records `r.value.1`, the exponent, as an `Int`, negative where a minus was read. The
absent case arises both where the text does not begin with `e` or `E` and where it has run out.
`expSign_sound` supplies which of `Exp.bare`, `Exp.plus` and `Exp.minus` applies, and
`digits_sound` the run of digits each requires.
-/
theorem expPart_sound {p : s.Pos} {r : Consumed (Int × Nat) p} (h : expPart p = .ok r) :
    Spec.Exp (remaining p) r.value.1 (remaining r.pos) := by
  rw [expPart] at h
  split at h
  · next e q he =>
    split at h
    · next hcond =>
      have hE : e = 'e' ∨ e = 'E' := by
        rcases Bool.or_eq_true .. ▸ hcond with h' | h'
        · exact .inl (eq_of_beq h')
        · exact .inr (eq_of_beq h')
      split at h
      · next negative w hsign hs =>
        split at h
        · next c t hd =>
          split at h
          · next hdig =>
            injection h with h
            have hdigs := digits_sound hd hdig
            rw [remaining_step he, ← h]
            rcases expSign_sound q with ⟨hneg, hpos⟩ | ⟨hneg, hplus⟩ | ⟨hneg, hminus⟩
            · simp only [hs] at hneg hpos
              subst hneg
              subst hpos
              simpa using Spec.Exp.bare hE hdigs
            · simp only [hs] at hneg hplus
              subst hneg
              rw [hplus]
              simpa using Spec.Exp.plus hE hdigs
            · simp only [hs] at hneg hminus
              subst hneg
              rw [hminus]
              simpa using Spec.Exp.minus hE hdigs
          · simp at h
        · simp at h
    · injection h with h
      rw [← h]
      exact Spec.Exp.absent
  · injection h with h
    rw [← h]
    exact Spec.Exp.absent


/--
The four parts of a number, assembled after a sign that has already been read, are a `number` of
the grammar. Factoring the sign out is what lets one proof serve both the negative and the
non-negative branch of the scanner.

`hsign : Spec.Sign t neg (remaining p)` says the caller has already derived the sign, taking the
text `t` down to the text at `p`, with `neg` recording it. `h` says the rest of the number scanned
successfully. The conclusion is a `Num` derivation from `t`, which is the text before the sign
rather than at `p`, recording the value the scanner computed. The three part soundness claims
supply the rest, and `Num.mk` requires them threaded in exactly this order.
-/
private theorem unsignedNumber_sound {cfg : Config} {p : s.Pos} {neg : Bool} {t : List Char}
    {res : Scanned Number p} (hsign : Spec.Sign t neg (remaining p))
    (h : unsignedNumber cfg p neg = .ok res) : Spec.Num t res.value (remaining res.pos) := by
  rw [unsignedNumber] at h
  split at h
  · simp at h
  · next i hi =>
    split at h
    · simp at h
    · next f hf =>
      split at h
      · simp at h
      · next x hx =>
        split at h
        · simp at h
        · injection h with h
          rw [← h]
          exact Spec.Num.mk hsign (intPart_sound hi) (fracPart_sound hf) (expPart_sound hx)

/--
What the scanner accepts as a number is a `number` of the grammar, denoting the value it returns.
It is what the value machine calls on seeing a minus or a digit, and it is where the number half
of soundness is complete.

`h : number cfg p = .ok res` says the scan succeeded. The `Spec.Num` derivation runs from the text
at `p`, records `res.value`, and leaves what remains where the scan stopped. The two branches are
a leading `'-'`, where `Sign.minus` is supplied and the text before it accounted for by
`remaining_step`, and everything else, where `Sign.absent` leaves the text unchanged. `cfg`
appears only in the digit limit, which affects whether the scan succeeds and not what it denotes.
-/
theorem number_sound {cfg : Config} {p : s.Pos} {res : Scanned Number p}
    (h : number cfg p = .ok res) : Spec.Num (remaining p) res.value (remaining res.pos) := by
  rw [number] at h
  split at h
  · next q hc =>
    split at h
    · simp at h
    · next r hr =>
      injection h with h
      have hs : Spec.Sign (remaining p) true (remaining q) := by
        rw [remaining_step hc]
        exact Spec.Sign.minus
      rw [← h]
      simpa using unsignedNumber_sound (t := remaining p) hs hr
  · exact unsignedNumber_sound Spec.Sign.absent h
  · simp at h


/-! ## Strings -/

/--
A hexadecimal digit the scanner reads is one the grammar values the same way. `Hex4` is stated
through `hexVal?`, so each of the four digits has to be produced together with the character it
came from.

`h : hexDigit? p = some r` says the scan succeeded with the value `r.value`. The conclusion
produces the character `c`, together with `Spec.hexVal? c = some r.value` and the equation putting
`c` at the head of what remained, so both the value and the single character consumed are pinned
down. The character is existentially quantified because the scanner does not return it.
-/
private theorem hexDigit?_sound {p : s.Pos} {r : Scanned Nat p} (h : hexDigit? p = some r) :
    ∃ c, Spec.hexVal? c = some r.value ∧ remaining p = c :: remaining r.pos := by
  rw [hexDigit?] at h
  split at h
  · next c q hc =>
    split at h
    · next v hv =>
      injection h with h
      rw [← h]
      exact ⟨c, hv, remaining_step hc⟩
    · simp at h
  · simp at h

/--
Four hexadecimal digits the scanner reads are a `4HEXDIG` of the grammar, denoting the value it
returns. It is the body of a `\u` escape, and both the single-escape rule and the surrogate-pair
rule are built on it.

`h : hex4? p = some r` says all four digits scanned. The `Spec.Hex4` derivation consumes exactly
four characters from the text at `p` and records the combined value `r.value`. Each digit comes
from `hexDigit?_sound`, and the four characters are chained by rewriting with the four
`remaining_step` equations before `Hex4.mk` is applied.
-/
theorem hex4?_sound {p : s.Pos} {r : Scanned Nat p} (h : hex4? p = some r) :
    Spec.Hex4 (remaining p) r.value (remaining r.pos) := by
  rw [hex4?] at h
  split at h
  · simp at h
  · next r₁ h₁ =>
    split at h
    · simp at h
    · next r₂ h₂ =>
      split at h
      · simp at h
      · next r₃ h₃ =>
        split at h
        · simp at h
        · next r₄ h₄ =>
          injection h with h
          obtain ⟨c₁, hv₁, hr₁⟩ := hexDigit?_sound h₁
          obtain ⟨c₂, hv₂, hr₂⟩ := hexDigit?_sound h₂
          obtain ⟨c₃, hv₃, hr₃⟩ := hexDigit?_sound h₃
          obtain ⟨c₄, hv₄, hr₄⟩ := hexDigit?_sound h₄
          rw [← h, hr₁, hr₂, hr₃, hr₄]
          exact Spec.Hex4.mk hv₁ hv₂ hv₃ hv₄


/--
A whole `\uXXXX` escape the scanner reads is a backslash, a `u`, and a `4HEXDIG` of the grammar.
The scanner looks for a second escape when the first names a high surrogate, and the pair rule
needs that second one in exactly this shape.

`h : escapeHex4? p = some r` says the escape scanned. The conclusion produces the text `t` after
the `\u` with `remaining p = '\\' :: 'u' :: t` and a `Hex4` derivation from `t`. Splitting the two
leading characters out is what lets the surrogate-pair constructor, which mentions them
explicitly, be applied.
-/
private theorem escapeHex4?_sound {p : s.Pos} {r : Scanned Nat p} (h : escapeHex4? p = some r) :
    ∃ t, remaining p = '\\' :: 'u' :: t ∧ Spec.Hex4 t r.value (remaining r.pos) := by
  rw [escapeHex4?] at h
  split at h
  · next q hc =>
    split at h
    · next w hu =>
      split at h
      · next hh hx =>
        injection h with h
        refine ⟨remaining w, ?_, ?_⟩
        · rw [remaining_step hc, remaining_step hu]
        · rw [← h]
          exact hex4?_sound hx
      · simp at h
    · simp at h
  · simp at h

/--
A hexadecimal digit's value is below sixteen. Four such values are combined into a code point, and
that combination has to be shown to stay inside the range a `Char` admits.

`h : Spec.hexVal? c = some v` says `c` is a hexadecimal digit with value `v`, and `v < 16` bounds
it. The three branches of `hexVal?` are the decimal digits, the lower-case letters and the
upper-case ones; each is bounded by arithmetic on the code points, which the six literal
equalities at the head of the proof supply.
-/
private theorem hexVal?_lt {c : Char} {v : Nat} (h : Spec.hexVal? c = some v) : v < 16 := by
  have h0 : ('0' : Char).toNat = 48 := rfl
  have h9 : ('9' : Char).toNat = 57 := rfl
  have ha : ('a' : Char).toNat = 97 := rfl
  have hf : ('f' : Char).toNat = 102 := rfl
  have hA : ('A' : Char).toNat = 65 := rfl
  have hF : ('F' : Char).toNat = 70 := rfl
  rw [Spec.hexVal?] at h
  split at h
  · next hc =>
    injection h with h
    simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
      Char.toNat_val] at hc
    omega
  · split at h
    · next hc =>
      injection h with h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
        Char.toNat_val] at hc
      omega
    · split at h
      · next hc =>
        injection h with h
        simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le,
          Char.toNat_val] at hc
        omega
      · simp at h

/--
Four hexadecimal digits denote less than `0x10000`. This is what makes a `\uXXXX` escape name a
code point in the basic multilingual plane, and it is the bound the character construction needs.

`h : Spec.Hex4 t v r` gives the four digit values through the single constructor, each below
sixteen by `hexVal?_lt`. Since `v` is `v₁ * 4096 + v₂ * 256 + v₃ * 16 + v₄`, the bound
follows by arithmetic; the largest value the four digits can spell is `0xFFFF`.
-/
private theorem hex4_lt {t : List Char} {v : Nat} {r : List Char} (h : Spec.Hex4 t v r) :
    v < 65536 := by
  cases h with
  | mk h₁ h₂ h₃ h₄ =>
    have b₁ := hexVal?_lt h₁
    have b₂ := hexVal?_lt h₂
    have b₃ := hexVal?_lt h₃
    have b₄ := hexVal?_lt h₄
    omega

/--
A character built from a code point has that code point. The grammar's escape rules relate an
escape to a character by their numbers, so the construction has to be shown to preserve the number
it was given.

`hv : v < 1114112` puts `v` inside the Unicode range, and `h` says the construction succeeded. The
conclusion `c.toNat = v` is what `Ch.codePoint` and `Ch.surrogatePair` both ask for. The bound is
what makes the `UInt32` conversion faithful, and without it the equation could fail by wrapping.
-/
private theorem charOfCodePoint?_toNat {v : Nat} {c : Char} (hv : v < 1114112)
    (h : charOfCodePoint? v = some c) : c.toNat = v := by
  rw [charOfCodePoint?] at h
  split at h
  · injection h with h
    have hsize : v < UInt32.size := by
      have hs : UInt32.size = 4294967296 := rfl
      omega
    rw [← h, Char.toNat_mk, UInt32.toNat_ofNat_of_lt' hsize]
  · simp at h


/--
A two-character escape the scanner recognises is a `char` of the grammar denoting the same
character. There are eight of them and the scanner tests them in sequence, so each has to be
matched to its own constructor.

`h : escapeChar? c = some ch` says `c` is one of the eight escape letters and `ch` the character
it stands for. The conclusion `Spec.Ch ('\\' :: c :: r) ch r` consumes the backslash and the
letter and leaves an arbitrary `r`. The `u` escape is not among these, `escapeChar?` returning
`none` for it, which is what keeps the two `\u` rules out of this claim.
-/
private theorem escapeChar?_sound {c ch : Char} (h : escapeChar? c = some ch) (r : List Char) :
    Spec.Ch ('\\' :: c :: r) ch r := by
  rw [escapeChar?] at h
  split at h
  · next hc =>
    injection h with h
    rw [eq_of_beq hc, ← h]
    exact Spec.Ch.quote
  · split at h
    · next hc =>
      injection h with h
      rw [eq_of_beq hc, ← h]
      exact Spec.Ch.backslash
    · split at h
      · next hc =>
        injection h with h
        rw [eq_of_beq hc, ← h]
        exact Spec.Ch.solidus
      · split at h
        · next hc =>
          injection h with h
          rw [eq_of_beq hc, ← h]
          exact Spec.Ch.backspace
        · split at h
          · next hc =>
            injection h with h
            rw [eq_of_beq hc, ← h]
            exact Spec.Ch.formFeed
          · split at h
            · next hc =>
              injection h with h
              rw [eq_of_beq hc, ← h]
              exact Spec.Ch.lineFeed
            · split at h
              · next hc =>
                injection h with h
                rw [eq_of_beq hc, ← h]
                exact Spec.Ch.carriageReturn
              · split at h
                · next hc =>
                  injection h with h
                  rw [eq_of_beq hc, ← h]
                  exact Spec.Ch.tab
                · simp at h


/--
A value below `0x10000` is inside the Unicode range. It is the trivial step from what four
hexadecimal digits can spell to what a character may hold, stated so the single-escape case can
appeal to it by name.

`h : v < 65536` gives the conclusion `v < 1114112` by arithmetic. It is separated out because
`charOfCodePoint?_toNat` asks for the wider bound while `hex4_lt` supplies the narrower one.
-/
private theorem codePoint_bound {v : Nat} (h : v < 65536) : v < 1114112 := by omega

/--
A surrogate pair combines to a code point inside the Unicode range. Surrogate pairs are how
characters above the basic plane are written, and the arithmetic that recombines them has to be
shown not to escape the range.

`h₁ : hi ≤ 56319` and `h₂ : lo ≤ 57343` are the upper ends of the high and low surrogate
blocks, which the scanner has already checked. `combineSurrogates hi lo` unfolds to
`65536 + (hi - 55296) * 1024 + (lo - 56320)`, and the two bounds put it below 1114112, which is
the largest a pair can reach.
-/
private theorem combineSurrogates_bound {hi lo : Nat} (h₁ : hi ≤ 56319) (h₂ : lo ≤ 57343) :
    combineSurrogates hi lo < 1114112 := by
  have h : combineSurrogates hi lo = 65536 + (hi - 55296) * 1024 + (lo - 56320) := rfl
  omega

/--
Where reading a piece of a string reports the end, the character consumed was a quotation mark.
The literal's closing quote is what the body derivation must stop at, so the machine's `done`
signal has to be identified with that character.

The conclusion `remaining p = '"' :: remaining q` puts the quotation mark at the head of what
remained. Only one branch of `stringStep` produces `done`, the one that consumed a `'"'`, so every
other branch makes the hypothesis unsatisfiable rather than the conclusion true.
-/
private theorem stringStep_done_sound (p : s.Pos) :
    ∀ q, stringStep p = .done q → remaining p = '"' :: remaining q := by
  fun_cases stringStep p with
  | case2 w hc =>
    intro q h
    injection h with h
    subst h
    exact remaining_step hc
  | _ => intro q h; simp at h

/--
Where reading a piece of a string produces a character, that piece is a `char` of the grammar
denoting it. Four branches produce a character, spelled in one, two, six or twelve characters, so
each has to be matched to its constructor.

The conclusion `Spec.Ch (remaining p) c (remaining q)` consumes the piece and leaves the rest. The
unescaped branch is `Ch.unescaped` with the scanner's own check; the two-character escapes go
through `escapeChar?_sound`; the `\u` branch builds `Ch.codePoint` from `hex4?_sound` with
`charOfCodePoint?_toNat` under `codePoint_bound`; and the pair branch builds `Ch.surrogatePair`
from two `Hex4` derivations, the scanner's range tests, and `combineSurrogates_bound`.
-/
private theorem stringStep_char_sound (p : s.Pos) :
    ∀ c q, stringStep p = .char c q → Spec.Ch (remaining p) c (remaining q) := by
  fun_cases stringStep p with
  | case6 w hc r hu hex hx hrange ch hcp =>
    intro c q h
    injection h with hch hq
    subst hq
    have hhex := hex4?_sound hx
    have hlt := hex4_lt hhex
    have hbound := codePoint_bound (hex4_lt hhex)
    have hval : ch.toNat = hex.value := charOfCodePoint?_toNat hbound hcp
    rw [← hch, remaining_step hc, remaining_step hu]
    exact Spec.Ch.codePoint hhex hval
  | case9 w hc r hu hex hx hrange hhigh lo hlo hbounds ch hcp =>
    intro c q h
    injection h with hch hq
    subst hq
    have hhex := hex4?_sound hx
    obtain ⟨t, hpre, hhex2⟩ := escapeHex4?_sound hlo
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hrange
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbounds
    rw [hpre] at hhex
    have hbound := combineSurrogates_bound hhigh hbounds.2
    have hval : ch.toNat = combineSurrogates hex.value lo.value :=
      charOfCodePoint?_toNat hbound hcp
    rw [← hch, remaining_step hc, remaining_step hu]
    refine Spec.Ch.surrogatePair hhex hhex2 hrange.1 hhigh hbounds.1 hbounds.2 ?_
    rw [hval]
    rfl
  | case13 w hc e r hne hu ch he =>
    intro c q h
    injection h with hch hq
    subst hq
    rw [← hch, remaining_step hc, remaining_step hu]
    exact escapeChar?_sound he _
  | case14 e w hquote hesc hc hun =>
    intro c q h
    injection h with hch hq
    subst hq
    rw [← hch, remaining_step hc]
    exact Spec.Ch.unescaped hun
  | _ => intro c q h; simp at h


/--
The string loop, from any point in a literal's body, consumes a `*char` run ending at the closing
quotation mark, and appends exactly those characters to its accumulator. The loop builds a
`String` as it goes while the grammar collects a list, so the two can only be compared with the
accumulator left free.

`p` is the position reached, `acc` what has been built, and `h` the loop's bookkeeping bound. The
conclusion produces the characters `cs` still to come, a `Chars` derivation running from the text
at `p` to a remainder that begins with the closing quote, and `r.value.toList = acc.toList ++ cs`.
That quote is left in the remainder rather than consumed, which is what lets `Str.mk` be applied
outside. The three cases follow the loop: a failure, which contradicts success, the end, which
gives `Chars.nil`, and a character, which gives `Chars.cons`.
-/
private theorem string_go_sound {start : s.Pos} :
    ∀ (p : s.Pos) (acc : String) (h : p.remainingBytes ≤ start.remainingBytes)
      (r : Scanned String start), string.go start p acc h = .ok r →
      ∃ cs, Spec.Chars (remaining p) cs ('"' :: remaining r.pos) ∧
        r.value.toList = acc.toList ++ cs := by
  intro p acc h
  fun_induction string.go start p acc h with
  | case1 p acc h e hs =>
    intro r hr
    simp at hr
  | case2 p acc h q hs =>
    intro r hr
    injection hr with hr
    refine ⟨[], ?_, ?_⟩
    · rw [← hr, stringStep_done_sound p q hs]
      exact Spec.Chars.nil
    · rw [← hr]
      simp
  | case3 p acc h c q hs ih =>
    intro r hr
    obtain ⟨cs, hchars, hval⟩ := ih r hr
    refine ⟨c :: cs, Spec.Chars.cons (stringStep_char_sound p c q hs) hchars, ?_⟩
    rw [hval, String.toList_push]
    simp

/--
What the scanner reads after an opening quotation mark is a `*char` run of the grammar, ending at
the closing quote. It is the loop's invariant taken at the point the machine actually enters it.

`h : string p acc = .ok r` says the body scanned successfully. The conclusion produces the
characters `cs`, a `Chars` derivation from `remaining p` whose remainder begins with `'"'`, and
the equation relating the returned string to `acc` and `cs`. It is `string_go_sound` at the loop's
starting position, where the bookkeeping bound is reflexivity.
-/
theorem string_sound {p : s.Pos} {acc : String} {r : Scanned String p}
    (h : string p acc = .ok r) :
    ∃ cs, Spec.Chars (remaining p) cs ('"' :: remaining r.pos) ∧
      r.value.toList = acc.toList ++ cs :=
  string_go_sound p acc (Nat.le_refl _) r h


/--
What the scanner reads between quotation marks is a `string` of the grammar denoting the value it
returns. It is what the value machine calls on seeing a quotation mark, and what the member reader
calls for a field name.

`hc` says the character at `p` is the opening `'"'` and `q` the position after it; `h` says the
body scanned. `Spec.Str (remaining p) r.value (remaining r.pos)` consumes the whole literal, both
quotes included. `string_sound` supplies the body, and `String.ofList_toList` is what turns the
collected characters back into the very string the scanner returned rather than one merely equal
to it character by character.
-/
theorem str_sound {p q : s.Pos} {r : Scanned String q} (hc : step? p = some ('"', q))
    (h : string q "" = .ok r) : Spec.Str (remaining p) r.value (remaining r.pos) := by
  obtain ⟨cs, hchars, hval⟩ := string_sound h
  have hstr : String.ofList cs = r.value := by
    have hcs : r.value.toList = cs := by simpa using hval
    rw [← hcs, String.ofList_toList]
  rw [remaining_step hc, ← hstr]
  exact Spec.Str.mk hchars


/-! ## The machine

A leaf scanner is a production of the grammar and nothing else, so its soundness is stated
directly. The machine is not: it holds what it has read so far in frames and closes them later,
so the text after a value has to finish every frame still on the stack before the parse is a
derivation at all.

Three relations say what that amounts to. `ElementsRest` and `MembersRest` describe the text
after a value or a member, which is the rest of the array or object around it and its closing
bracket. `Closes` describes the stack: each frame consumes its rest and hands the value it
completes to the frame outside it, and the empty stack is the whole value.
-/

/-- The elements after one already read, and the closing bracket. -/
inductive ElementsRest : List Char → List Json → List Char → Prop where
  | close {t r} : Spec.EndArray t r → ElementsRest t [] r
  | more {t t₁ t₂ v vs r} : Spec.ValueSeparator t t₁ → Spec.Value t₁ v t₂ →
      ElementsRest t₂ vs r → ElementsRest t (v :: vs) r

/-- The members after one already read, and the closing brace. -/
inductive MembersRest : List Char → List (String × Json) → List Char → Prop where
  | close {t r} : Spec.EndObject t r → MembersRest t [] r
  | more {t t₁ t₂ m ms r} : Spec.ValueSeparator t t₁ → Spec.Member t₁ m t₂ →
      MembersRest t₂ ms r → MembersRest t (m :: ms) r

@[expose] def ElementsEnd (t : List Char) (vs : List Json) (r : List Char) : Prop :=
  ∃ t', Spec.Elements t vs t' ∧ Spec.EndArray t' r

@[expose] def MembersEnd (t : List Char) (ms : List (String × Json)) (r : List Char) : Prop :=
  ∃ t', Spec.Members t ms t' ∧ Spec.EndObject t' r

/--
A value followed by the rest of its array is that array's element list, up to the closing bracket.
The machine reads one element and defers the rest, so its state has to be turned into a derivation
that covers the elements as a whole.

`hrest : ElementsRest t₂ vs r` describes the text after the first value: the remaining elements
`vs`, each preceded by a separator, and then the closing bracket, leaving `r`. Given a `Value`
derivation ending at `t₂`, the conclusion `ElementsEnd t₁ (v :: vs) r` produces an `Elements`
derivation for the whole list together with the `EndArray` after it. The induction is on `hrest`,
whose `close` case gives `Elements.one` and whose `more` case gives `Elements.more`.
-/
theorem elementsEnd_cons {t₂ r : List Char} {vs : List Json}
    (hrest : ElementsRest t₂ vs r) :
    ∀ {t₁ : List Char} {v : Json}, Spec.Value t₁ v t₂ → ElementsEnd t₁ (v :: vs) r := by
  induction hrest with
  | close hend => exact fun hv => ⟨_, Spec.Elements.one hv, hend⟩
  | more hsep hv₂ _ ih =>
    intro t₁ v hv
    obtain ⟨t', hels, hend⟩ := ih hv₂
    exact ⟨t', Spec.Elements.more hv hsep hels, hend⟩

/--
A member followed by the rest of its object is that object's member list, up to the closing brace.
It is the object counterpart of the array case, and needed separately because `Members` is a
distinct production over differently shaped contents.

`hrest : MembersRest t₂ ms r` describes the text after the first member: the remaining members
`ms`, each preceded by a separator, and then the closing brace. Given a `Member` derivation ending
at `t₂`, the conclusion produces a `Members` derivation for the whole list together with the
`EndObject` after it. The induction is on `hrest`, giving `Members.one` and `Members.more`.
-/
theorem membersEnd_cons {t₂ r : List Char} {ms : List (String × Json)}
    (hrest : MembersRest t₂ ms r) :
    ∀ {t₁ : List Char} {m : String × Json}, Spec.Member t₁ m t₂ → MembersEnd t₁ (m :: ms) r := by
  induction hrest with
  | close hend => exact fun hm => ⟨_, Spec.Members.one hm, hend⟩
  | more hsep hm₂ _ ih =>
    intro t₁ m hm
    obtain ⟨t', hms, hend⟩ := ih hm₂
    exact ⟨t', Spec.Members.more hm hsep hms, hend⟩

/-- What the frames still on the stack demand of the text after the value just read. -/
@[expose] def Closes : List Frame → Json → List Char → Json → List Char → Prop
  | [], v, t, j, r => j = v ∧ r = t
  | .arr elems :: outer, v, t, j, r =>
      ∃ vs t', ElementsRest t vs t' ∧ Closes outer (.arr (elems.push v ++ vs.toArray)) t' j r
  | .obj fields _ name :: outer, v, t, j, r =>
      ∃ ms t', MembersRest t ms t' ∧
        Closes outer (.obj (fields.push (name, v) ++ ms.toArray)) t' j r


/-!
Each of the machine's three functions calls the others, and every call is made at a position
strictly further on, so a single induction on how much text is left carries all three at once.
-/

/--
The whitespace skipper's result, taken apart into its fields, still carries its derivation. The
machine pattern matches on the record `skipWs` returns, so the derivation has to be re-attached to
the position that match produced.

`h : skipWs q = ⟨u, w, hw⟩` names the components of the result, `w` being the position
reached. The conclusion `Spec.Ws (remaining q) (remaining w)` is `ws_skipWs` rewritten along that
equation. Nothing new is proved; what it provides is the derivation in terms of the variable the
machine's own pattern bound.
-/
private theorem ws_of_skipWs {q w : s.Pos} {u : Unit} {hw : w.remainingBytes ≤ q.remainingBytes}
    (h : skipWs q = ⟨u, w, hw⟩) : Spec.Ws (remaining q) (remaining w) := by
  have hws := ws_skipWs q
  rw [h] at hws
  exact hws

/--
A structural character with the whitespace the scanner passed over on either side is a token of
the grammar. Every bracket, comma and colon the machine reads has this shape, so one statement
serves them all.

`hlead` is the whitespace from `p` to `q`, `hstep` says the character `t` sits at `q` with `r`
after it, and `htrail` is the whitespace from `r` to `r'`. The conclusion assembles them into a
`Spec.Token t` derivation from the text at `p` to the text at `r'`; `remaining_step` is what
places `t` between the two runs. Either run may be empty, `Ws.nil` being a derivation, so this
covers the compact case as well.
-/
private theorem token_of {t : Char} {p q r r' : s.Pos}
    (hlead : Spec.Ws (remaining p) (remaining q)) (hstep : step? q = some (t, r))
    (htrail : Spec.Ws (remaining r) (remaining r')) : Spec.Token t (remaining p) (remaining r') :=
  Spec.Token.mk (remaining_step hstep ▸ hlead) htrail

private def ValueSound (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (stack : List Frame) (j : Json) (rp : s.Pos),
    value cfg p depth stack = .ok (j, rp) →
      ∃ v t, Spec.Value (remaining p) v t ∧ Closes stack v t j (remaining rp)

private def ContinueSound (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (v : Json) (depth : Nat) (stack : List Frame) (j : Json) (rp : s.Pos),
    continueWith cfg v p depth stack = .ok (j, rp) →
      Closes stack v (remaining p) j (remaining rp)

private def MemberSound (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (fields : Array (String × Json)) (seen : Std.HashSet String)
      (stack : List Frame) (j : Json) (rp : s.Pos),
    member cfg p depth fields seen stack = .ok (j, rp) →
      ∃ m ms t₁ t, Spec.Member (remaining p) m t₁ ∧ MembersRest t₁ ms t ∧
        Closes stack (.obj (fields ++ (m :: ms).toArray)) t j (remaining rp)

/--
Every accepting run of the machine has a derivation behind it, at any point in the run and with
any stack of frames. `value`, `continueWith` and `member` call one another, so none can be
described alone; this is the statement provable of all three together, and the entry points below
are its instances.

`n` bounds the bytes remaining and the induction runs on `n`, every call being made at a strictly
later position. Each conjunct pairs a derivation with what the stack still demands. `ValueSound`
says a successful `value` yields some `v` derivable from the text at `p`, leaving `t`, such that
`Closes stack v t j (remaining rp)`: the frames still on the stack consume `t` and build `j` out
of `v`. `ContinueSound` says the same of a value already in hand, and `MemberSound` of a member
being read, whose conclusion also carries the members after it. `Closes` is stated by recursion on
the stack, so the empty stack case is what finally identifies `j` with the value read. The bound
cannot empty the claim, any position satisfying it at its own remaining bytes.
-/
private theorem machine_sound (cfg : Config) :
    ∀ (n : Nat) (p : s.Pos), p.remainingBytes ≤ n →
      ValueSound cfg p ∧ ContinueSound cfg p ∧ MemberSound cfg p := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · intro depth stack j rp
      fun_cases value cfg p depth stack with
      | case1 => intro h; simp at h
      | case2 q hc _ r hr hex =>
        intro h
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 .null depth stack j rp h
        have ht : remaining p = 'n' :: 'u' :: 'l' :: 'l' :: remaining r := by
          simp [remaining_step hc, expect?_eq hex]
        exact ⟨.null, remaining r, by rw [ht]; exact Spec.Value.null, hcont⟩
      | case3 => intro h; simp at h
      | case4 q hc _ r hr hex =>
        intro h
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 (.bool true) depth stack j rp h
        have ht : remaining p = 't' :: 'r' :: 'u' :: 'e' :: remaining r := by
          simp [remaining_step hc, expect?_eq hex]
        exact ⟨.bool true, remaining r, by rw [ht]; exact Spec.Value.true_, hcont⟩
      | case5 => intro h; simp at h
      | case6 q hc _ r hr hex =>
        intro h
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 (.bool false) depth stack j rp h
        have ht : remaining p = 'f' :: 'a' :: 'l' :: 's' :: 'e' :: remaining r := by
          simp [remaining_step hc, expect?_eq hex]
        exact ⟨.bool false, remaining r, by rw [ht]; exact Spec.Value.false_, hcont⟩
      | case7 => intro h; simp at h
      | case8 => intro h; simp at h
      | case9 q hc text r hr hstr =>
        intro h
        have hlt : r.remainingBytes < n := by have := step?_lt hc; omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 (.str text) depth stack j rp h
        exact ⟨.str text, remaining r, Spec.Value.str (str_sound hc hstr), hcont⟩
      | case10 => intro h; simp at h
      | case11 q hc _ _ w hw hsw after hb =>
        intro h
        have hlt : after.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        have hcont := (ih _ hlt after (Nat.le_refl _)).2.1 (.arr #[]) depth stack j rp h
        exact ⟨.arr #[], remaining after,
          Spec.Value.arr (Spec.Arr.empty (token_of Spec.Ws.nil hc (ws_of_skipWs hsw))
            (token_of Spec.Ws.nil hb Spec.Ws.nil)), hcont⟩
      | case12 q hc _ _ w hw hsw _ =>
        intro h
        have hlt : w.remainingBytes < n := by have := step?_lt hc; omega
        obtain ⟨v, t, hv, hcl⟩ :=
          (ih _ hlt w (Nat.le_refl _)).1 (depth + 1) (.arr #[] :: stack) j rp h
        simp only [Closes] at hcl
        obtain ⟨vs, t', hrest, hcl⟩ := hcl
        obtain ⟨t'', hels, hend⟩ := elementsEnd_cons hrest hv
        refine ⟨.arr (v :: vs).toArray, t',
          Spec.Value.arr (Spec.Arr.items (token_of Spec.Ws.nil hc (ws_of_skipWs hsw)) hels hend),
          ?_⟩
        simpa using hcl
      | case13 => intro h; simp at h
      | case14 q hc _ _ w hw hsw after hb =>
        intro h
        have hlt : after.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        have hcont := (ih _ hlt after (Nat.le_refl _)).2.1 (.obj #[]) depth stack j rp h
        exact ⟨.obj #[], remaining after,
          Spec.Value.obj (Spec.Object.empty (token_of Spec.Ws.nil hc (ws_of_skipWs hsw))
            (token_of Spec.Ws.nil hb Spec.Ws.nil)), hcont⟩
      | case15 q hc _ _ w hw hsw _ =>
        intro h
        have hlt : w.remainingBytes < n := by have := step?_lt hc; omega
        obtain ⟨m, ms, t₁, t, hm, hrest, hcl⟩ :=
          (ih _ hlt w (Nat.le_refl _)).2.2 (depth + 1) #[] ∅ stack j rp h
        obtain ⟨t'', hms, hendo⟩ := membersEnd_cons hrest hm
        refine ⟨.obj (m :: ms).toArray, t,
          Spec.Value.obj (Spec.Object.members (token_of Spec.Ws.nil hc (ws_of_skipWs hsw)) hms
            hendo), ?_⟩
        simpa using hcl
      | case16 => intro h; simp at h
      | case17 _ _ _ _ _ _ _ _ hc _ m r hr hnum =>
        intro h
        have hlt : r.remainingBytes < n := by omega
        have hcont := (ih _ hlt r (Nat.le_refl _)).2.1 (.num m) depth stack j rp h
        exact ⟨.num m, remaining r, Spec.Value.num (number_sound hnum), hcont⟩
      | case18 => intro h; simp at h
    · intro v depth stack j rp
      fun_cases continueWith cfg v p depth stack with
      | case1 =>
        intro h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨h.1.symm, by rw [h.2]⟩
      | case2 elems outer _ w hw hsw after hb _ w₂ hw₂ hsw₂ =>
        intro h
        have hlt : w₂.remainingBytes < n := by have := step?_lt hb; omega
        obtain ⟨v₂, t, hv, hcl⟩ :=
          (ih _ hlt w₂ (Nat.le_refl _)).1 depth (.arr (elems.push v) :: outer) j rp h
        simp only [Closes] at hcl ⊢
        obtain ⟨vs, t', hrest, hcl⟩ := hcl
        refine ⟨v₂ :: vs, t',
          ElementsRest.more (token_of (ws_of_skipWs hsw) hb (ws_of_skipWs hsw₂)) hv hrest, ?_⟩
        simpa using hcl
      | case3 elems outer _ w hw hsw after hb =>
        intro h
        have hlt : after.remainingBytes < n := by have := step?_lt hb; omega
        have hcont :=
          (ih _ hlt after (Nat.le_refl _)).2.1 (.arr (elems.push v)) (depth - 1) outer j rp h
        simp only [Closes]
        exact ⟨[], remaining after,
          ElementsRest.close (token_of (ws_of_skipWs hsw) hb Spec.Ws.nil), by simpa using hcont⟩
      | case4 => intro h; simp at h
      | case5 => intro h; simp at h
      | case6 fields seen name outer _ w hw hsw after hb _ w₂ hw₂ hsw₂ =>
        intro h
        have hlt : w₂.remainingBytes < n := by have := step?_lt hb; omega
        obtain ⟨m, ms, t₁, t, hm, hrest, hcl⟩ :=
          (ih _ hlt w₂ (Nat.le_refl _)).2.2 depth (fields.push (name, v)) seen outer j rp h
        simp only [Closes]
        exact ⟨m :: ms, t,
          MembersRest.more (token_of (ws_of_skipWs hsw) hb (ws_of_skipWs hsw₂)) hm hrest, hcl⟩
      | case7 fields seen name outer _ w hw hsw after hb =>
        intro h
        have hlt : after.remainingBytes < n := by have := step?_lt hb; omega
        have hcont := (ih _ hlt after (Nat.le_refl _)).2.1 (.obj (fields.push (name, v)))
          (depth - 1) outer j rp h
        simp only [Closes]
        exact ⟨[], remaining after,
          MembersRest.close (token_of (ws_of_skipWs hsw) hb Spec.Ws.nil), by simpa using hcont⟩
      | case8 => intro h; simp at h
      | case9 => intro h; simp at h
    · intro depth fields seen stack j rp
      fun_cases member cfg p depth fields seen stack with
      | case1 => intro h; simp at h
      | case2 => intro h; simp at h
      | case3 q hc name k hk hstr _ _ w hw hsw after hb _ w₂ hw₂ hsw₂ =>
        intro h
        have hlt : w₂.remainingBytes < n := by
          have := step?_lt hc
          have := step?_lt hb
          omega
        obtain ⟨v, t, hv, hcl⟩ := (ih _ hlt w₂ (Nat.le_refl _)).1 depth
          (.obj fields (seen.insert name) name :: stack) j rp h
        simp only [Closes] at hcl
        obtain ⟨ms, t', hrest, hcl⟩ := hcl
        refine ⟨(name, v), ms, t, t',
          Spec.Member.mk (str_sound hc hstr)
            (token_of (ws_of_skipWs hsw) hb (ws_of_skipWs hsw₂)) hv, hrest, ?_⟩
        simpa using hcl
      | case4 => intro h; simp at h
      | case5 => intro h; simp at h
      | case6 => intro h; simp at h
      | case7 => intro h; simp at h


/-! ## Text

`Spec.Text` is one value with whitespace either side of it and nothing else, which is what the
entry points read.
-/

/--
A successful parse from a given position is a `Text` derivation of the text there. `parseFrom`
starts the machine with an empty stack and then requires nothing but whitespace after the value,
which is exactly the shape of `Text`.

`h : parseFrom cfg start = .ok j` says the parse succeeded with `j`. The conclusion says the text
at `start` is whitespace, a value denoting `j`, and whitespace, with nothing left over. The
leading whitespace is `ws_skipWs` at `start`; the value is `machine_sound` with an empty stack,
where `Closes` collapses to `j` being the value read; the trailing whitespace is `ws_skipWs` again
followed by `remaining_none`, the parse having required the text to be exhausted.
-/
theorem text_parseFrom {cfg : Config} {start : s.Pos} {j : Json}
    (h : parseFrom cfg start = .ok j) : Spec.Text (remaining start) j := by
  simp only [parseFrom] at h
  split at h
  · simp at h
  · next j' p hv =>
    split at h
    · next hend =>
      obtain ⟨v, t, hval, hcl⟩ :=
        (machine_sound cfg _ (skipWs start).pos (Nat.le_refl _)).1 0 [] j' p hv
      simp only [Closes] at hcl
      obtain ⟨hj, ht⟩ := hcl
      injection h with hjj
      refine ⟨_, t, ws_skipWs start, ?_, ?_⟩
      · rw [← hjj, hj]
        exact hval
      · rw [← ht]
        exact remaining_none hend ▸ ws_skipWs p
    · simp at h

end

/--
What the parser accepts is a text of the grammar, save that a byte order mark it was configured to
ignore is no part of one. RFC 8259 permits ignoring a leading `U+FEFF`, and the parser does so by
default, so the statement has to allow for a character the grammar does not.

`h : parse s cfg = .ok j` says the parse succeeded. The conclusion produces the text `t` with
`Spec.Text t j`, and says `s.toList` is either `t` itself or `t` behind a single `U+FEFF`. The
second alternative is reached only where the configuration allowed the mark and the text began
with one; the character is identified by its code point, which is what `Char.toNat_inj` converts
into an equality of characters.
-/
theorem text_parse {s : String} {cfg : Config} {j : Json} (h : parse s cfg = .ok j) :
    ∃ t, Spec.Text t j ∧ (s.toList = t ∨ s.toList = Char.ofNat 0xFEFF :: t) := by
  cases hc : step? s.startPos with
  | none =>
    simp only [parse, hc] at h
    exact ⟨_, text_parseFrom h, Or.inl remaining_startPos.symm⟩
  | some cq =>
    obtain ⟨c, q⟩ := cq
    simp only [parse, hc] at h
    split at h
    · next hbom =>
      refine ⟨_, text_parseFrom h, Or.inr ?_⟩
      have hval : c.toNat = 0xFEFF := by
        simp only [Bool.and_eq_true] at hbom
        exact eq_of_beq hbom.2
      have hbomChar : c = Char.ofNat 0xFEFF :=
        Char.toNat_inj.mp (by rw [hval]; rfl)
      rw [← remaining_startPos, remaining_step hc, hbomChar]
    · exact ⟨_, text_parseFrom h, Or.inl remaining_startPos.symm⟩

/--
With no byte order mark to set aside, what the parser accepts is a text of the grammar. This is
the form soundness is used in: a claim about the string itself, with no leftover character to
account for.

`hbom : cfg.ignoreBOM = false` is what removes the alternative, the parser then starting at the
first character whatever it is. `h` says the parse succeeded with `j`, and `Spec.TextOf s j` says
the string's characters form a text denoting `j`. Both branches, an empty string and a non-empty
one, reduce through `remaining_startPos` to `text_parseFrom` at the start.
-/
theorem textOf_parse {s : String} {cfg : Config} {j : Json} (hbom : cfg.ignoreBOM = false)
    (h : parse s cfg = .ok j) : Spec.TextOf s j := by
  cases hc : step? s.startPos with
  | none =>
    simp only [parse, hc] at h
    show Spec.Text s.toList j
    rw [← remaining_startPos]
    exact text_parseFrom h
  | some cq =>
    obtain ⟨c, q⟩ := cq
    simp only [parse, hc, hbom] at h
    show Spec.Text s.toList j
    rw [← remaining_startPos]
    exact text_parseFrom h


/--
The value the parser returns is the value the grammar names, there being no other. Soundness on
its own says the text derives what the parser returned; this adds that the text derives nothing
else, which is what makes "the value of this text" a definite description.

`hbom` again removes the byte order mark alternative. `h` says the parse returned `j`, and `ht`
says the same string is a text denoting `j'`, from any source whatever. The conclusion `j = j'`
composes `textOf_parse` with `Spec.textOf_unique`, and it is the uniqueness rather than the
soundness that is doing the work here.
-/
theorem eq_of_textOf {s : String} {cfg : Config} {j j' : Json} (hbom : cfg.ignoreBOM = false)
    (h : parse s cfg = .ok j) (ht : Spec.TextOf s j') : j = j' :=
  Spec.textOf_unique (textOf_parse hbom h) ht


/--
Every number the parser returns is canonical, whatever the text spelled. This is what lets a
parsed value be compared, ordered and hashed structurally, and it is what discharges the printer's
precondition for a value that came from text.

`h : parse s cfg = .ok j` says the parse succeeded. `CanonicalNumbers j` says every number
anywhere within `j` is in canonical form. It follows from `text_parse` and
`Spec.canonicalNumbers_of_text`; a byte order mark, which the first of those leaves undetermined,
does not matter, since the derivation it produces is of the value either way. No hypothesis on
`cfg` is needed, canonicity being a property of the grammar rather than of any setting.
-/
theorem canonicalNumbers_parse {s : String} {cfg : Config} {j : Json} (h : parse s cfg = .ok j) :
    CanonicalNumbers j := by
  obtain ⟨t, ht, -⟩ := text_parse h
  exact Spec.canonicalNumbers_of_text ht

/--
Bytes the parser accepts are UTF-8 for a text of the grammar. RFC 8259 section 8.1 requires UTF-8
for interchange, and this is where that requirement is discharged: the byte level is handled by
decoding first and reasoning about the resulting string.

`hbom` removes the byte order mark alternative, as in the string case, and `h` says that
`parseBytes b cfg` succeeded with `j`. The conclusion produces the `text` that
`String.fromUTF8? b` returns, so the bytes are asserted to be valid UTF-8, and
`Spec.TextOf text j` alongside it. Invalid bytes make the hypothesis unsatisfiable rather than the
conclusion false, `parseBytes` refusing them before any parsing is attempted.
-/
theorem textOf_parseBytes {b : ByteArray} {cfg : Config} {j : Json} (hbom : cfg.ignoreBOM = false)
    (h : parseBytes b cfg = .ok j) :
    ∃ text, String.fromUTF8? b = some text ∧ Spec.TextOf text j := by
  rw [parseBytes] at h
  split at h
  · next text hs => exact ⟨text, hs, textOf_parse hbom h⟩
  · simp at h

end Json.Parser
