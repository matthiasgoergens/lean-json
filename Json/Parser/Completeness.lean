/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser.Soundness
public import Json.Parser.UniqueKeys
public import Json.Spec.Follow
public import Json.Spec.Unambiguity

public section

@[expose] section

namespace Json.Parser

variable {s : String}

/-!
The other direction: what the grammar derives, the parser accepts.

Three things shape the work. The value needs no tracking, since `parse_eq_of_isOk` gets it from
soundness and unambiguity together, which leaves only the obligation that a derivable text is
never refused. A scanner has to be shown maximal, which soundness never needed: `Ws` relates a
text to any of its whitespace-suffixes, while `skipWs` lands on exactly one of them, so the two
are tied together by what the scanner leaves rather than by what it consumes. And a derivation
can have taken whitespace the parser has not yet looked at, so what the machine concludes about
the position it stops at is stated with `Ws` rather than with equality.
-/

/--
On a text the grammar derives, returning anything at all is returning the right thing, there being
one value the text names and soundness saying the returned one is among them. This is what lets
the rest of the module ignore the value entirely and prove only that the parser does not fail,
which is a far smaller obligation than tracking a value through the machine.

`hbom` removes the byte order mark case, `ht` says `s` derives `j`, and `hok` says the parse
succeeded without saying with what. The conclusion names the result as `j`. It is `eq_of_textOf`,
soundness composed with uniqueness; `hok` is what excludes the error case, which is the only other
outcome a parse has.
-/
theorem parse_eq_of_isOk {cfg : Config} {j : Json} (hbom : cfg.ignoreBOM = false)
    (ht : Spec.TextOf s j) (hok : (parse s cfg).isOk) : parse s cfg = .ok j := by
  cases h : parse s cfg with
  | error e => rw [h] at hok; exact absurd hok (by simp [Except.isOk, Except.toBool])
  | ok j' => rw [eq_of_textOf hbom h ht]

/--
The whitespace skipper stops at a character that is not whitespace, or at the end of the text.
Soundness needed only that what it consumed was whitespace; completeness needs that it consumed
all of it, and this is the half that says so.

`Spec.NoWs (remaining (skipWs start).pos)` says the text left where the skipper stopped does not
begin with a whitespace character; where it stopped at the end of the text the condition holds
with nothing to check, which is one of the two stopping cases rather than an exception. The proof
follows `skipWs.go`, whose stopping cases are exactly a non-whitespace character and the end.
-/
theorem noWs_skipWs (start : s.Pos) : Spec.NoWs (remaining (skipWs start).pos) := by
  have go : ∀ (p : s.Pos) (h : p.remainingBytes ≤ start.remainingBytes),
      Spec.NoWs (remaining (skipWs.go start p h).pos) := by
    intro p h
    fun_induction skipWs.go start p h with
    | case1 p h c q hc hws ih => exact ih
    | case2 p h c q hc hws =>
      intro c' t hct
      rw [remaining_step hc] at hct
      simp only [List.cons.injEq] at hct
      obtain ⟨rfl, -⟩ := hct
      simpa using hws
    | case3 p h hc =>
      intro c' t hct
      rw [remaining_none hc] at hct
      exact absurd hct (by simp)
  exact go start (Nat.le_refl _)

/--
Whatever whitespace a derivation passed over, the skipper passes over exactly that much. `Ws`
relates a text to any of its whitespace-suffixes while the skipper lands on one particular suffix,
so the two can only be matched through where each of them stops.

`h` is a derivation from the text at `p` to `t`, and `hn` says `t` begins with no whitespace. The
conclusion `remaining (skipWs p).pos = t` is an equality of texts. It is `Spec.Ws.eq_of_noWs` with
the skipper's own derivation and `noWs_skipWs` on one side and `h` and `hn` on the other; without
`hn` the derivation could have stopped short and the two would differ.
-/
theorem skipWs_complete {p : s.Pos} {t : List Char} (h : Spec.Ws (remaining p) t)
    (hn : Spec.NoWs t) : remaining (skipWs p).pos = t :=
  Spec.Ws.eq_of_noWs (ws_skipWs p) h (noWs_skipWs p) hn


/--
Reading a character is taking the head off what remains. It is the converse of the correspondence
soundness uses: there a scanner step produced a `cons`, and here a `cons` produces a scanner step.

`h : remaining p = c :: t` says the text at `p` begins with `c`. The conclusion produces the
position `q` after it, with `step? p = some (c, q)` and `remaining q = t`. The `none` case of
`step?` is excluded because it would make the remainder empty, which `h` denies.
-/
theorem step_of_remaining {p : s.Pos} {c : Char} {t : List Char} (h : remaining p = c :: t) :
    ∃ q, step? p = some (c, q) ∧ remaining q = t := by
  cases hs : step? p with
  | none => rw [remaining_none hs] at h; exact absurd h (by simp)
  | some cq =>
    obtain ⟨c', q⟩ := cq
    have he := remaining_step hs
    rw [h] at he
    simp only [List.cons.injEq] at he
    obtain ⟨hcc, htt⟩ := he
    subst hcc
    exact ⟨q, rfl, htt.symm⟩

/-! ## Numbers -/

/--
The digit loop stops at a character that is not a digit, or at the end of the text. It is what
makes the loop maximal, which the uniqueness of a run of digits needs and soundness did not.

`Spec.NoDigit (remaining (digits start value count).pos)` says the text left where the loop
stopped does not begin with a digit; at the end of the text it holds with nothing to check. The
proof follows `digits.go`, whose two stopping cases are a non-digit and the end. Neither `value`
nor `count` bears on the conclusion, the loop's accumulator not affecting where it stops.
-/
theorem noDigit_digits (start : s.Pos) (value count : Nat) :
    Spec.NoDigit (remaining (digits start value count).pos) := by
  have go : ∀ (p : s.Pos) (v n : Nat) (h : p.remainingBytes ≤ start.remainingBytes),
      Spec.NoDigit (remaining (digits.go start p v n h).pos) := by
    intro p v n h
    fun_induction digits.go start p v n h with
    | case1 p v n h c q hc hd ih => exact ih
    | case2 p v n h c q hc hd =>
      intro c' t hct
      rw [remaining_step hc] at hct
      simp only [List.cons.injEq] at hct
      obtain ⟨rfl, -⟩ := hct
      simpa using hd
    | case3 p v n h hc =>
      intro c' t hct
      rw [remaining_none hc] at hct
      exact absurd hct (by simp)
  exact go start value count (Nat.le_refl _)

/--
Whatever run of digits a derivation took, the loop takes exactly that run, with the same value and
the same count. The grammar lets a run stop anywhere, so this is where its answer is pinned to the
loop's.

`hc` and `hd` say `c` is a digit at `p`, `h` derives `v` with `n` digits leaving `t`, and `hn`
says `t` begins with no digit. The conclusion gives both the loop's value pair and its stopping
position. It is `Spec.digits_unique` applied to the loop's own derivation, from `digits_sound`,
and to `h`, with `noDigit_digits` and `hn` as the two maximality conditions it requires.
-/
theorem digits_complete {p q : s.Pos} {c : Char} (hc : step? p = some (c, q))
    (hd : Spec.isDigit c = true) {v n : Nat} {t : List Char}
    (h : Spec.Digits (remaining p) v n t) (hn : Spec.NoDigit t) :
    (digits q (Spec.digitVal c) 1).value = (v, n) ∧
      remaining (digits q (Spec.digitVal c) 1).pos = t := by
  obtain ⟨hv, hnn, hr⟩ :=
    Spec.digits_unique (digits_sound hc hd) h (noDigit_digits q (Spec.digitVal c) 1) hn
  exact ⟨by rw [Prod.ext_iff]; exact ⟨hv, hnn⟩, hr⟩

/--
Whatever integer part a derivation read, the scanner reads, returning the same value and stopping
in the same place. It is the first of the number parts and the only one whose scan can fail.

`h` is an `Int'` derivation from the text at `p` leaving `t`, and `hn` says `t` begins with no
digit. The conclusion produces the result `r` with `intPart p = .ok r`, `r.value.1 = v` and
`remaining r.pos = t`, so success, value and position are all claimed. The digit count `r.value.2`
goes unmentioned, `Int'` recording none.
-/
theorem intPart_complete {p : s.Pos} {v : Nat} {t : List Char}
    (h : Spec.Int' (remaining p) v t) (hn : Spec.NoDigit t) :
    ∃ r : Scanned (Nat × Nat) p, intPart p = .ok r ∧ r.value.1 = v ∧ remaining r.pos = t := by
  obtain ⟨c, u, hcu, hd⟩ := Spec.int_head h
  obtain ⟨q, hq, hqu⟩ := step_of_remaining hcu
  rw [hcu] at h
  rw [intPart]
  split
  · next q' hz =>
    have hqq := hq.symm.trans hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hqq
    obtain ⟨rfl, rfl⟩ := hqq
    cases h with
    | zero => exact ⟨_, rfl, rfl, hqu⟩
    | digits hc _ => exact absurd hc (by decide)
  · next c' q' hne hz =>
    have hqq := hq.symm.trans hz
    simp only [Option.some.injEq, Prod.mk.injEq] at hqq
    obtain ⟨rfl, rfl⟩ := hqq
    split
    · next hdig =>
      cases h with
      | zero => exact absurd rfl hne
      | digits _ hdigs =>
        rw [← hcu] at hdigs
        obtain ⟨hval, hpos⟩ := digits_complete hq hdig hdigs hn
        exact ⟨_, rfl, by rw [hval], hpos⟩
    · next hdig => exact absurd hd hdig
  · next hz => rw [hq] at hz; exact absurd hz (by simp)

/--
Whatever fraction a derivation read, the scanner reads, the absent case included. That case is not
trivial: the scanner has to be shown to leave the position exactly where the derivation did.

`h` is a `Frac` derivation and `hn` says the remainder begins with neither a digit nor a `'.'`.
The conclusion produces `r` with `fracPart p = .ok r`, `r.value = (f, n)`, both value and digit
count, and `remaining r.pos = t`. Where the text does not begin with `'.'`, `Spec.frac_absent`
under `hn` forces the derivation to be the absent one and both sides to consume nothing.
-/
theorem fracPart_complete {p : s.Pos} {f n : Nat} {t : List Char}
    (h : Spec.Frac (remaining p) f n t) (hn : Spec.NoFrac t) :
    ∃ r : Consumed (Nat × Nat) p, fracPart p = .ok r ∧ r.value = (f, n) ∧ remaining r.pos = t := by
  rw [fracPart]
  split
  · next q hz =>
    rw [remaining_step hz] at h
    cases h with
    | absent => exact absurd rfl (hn _ _ rfl).2
    | present hdigs =>
      obtain ⟨c, w, hcw, hdg⟩ := Spec.digits_head hdigs
      obtain ⟨r', hr', hrw⟩ := step_of_remaining hcw
      split
      · next c' r'' hd2 =>
        have hqq := hr'.symm.trans hd2
        simp only [Option.some.injEq, Prod.mk.injEq] at hqq
        obtain ⟨rfl, rfl⟩ := hqq
        split
        · next hdig =>
          obtain ⟨hval, hpos⟩ := digits_complete hr' hdig hdigs (Spec.noDigit_of_noFrac hn)
          exact ⟨_, rfl, hval, hpos⟩
        · next hdig => exact absurd hdg hdig
      · next hd2 => rw [hr'] at hd2; exact absurd hd2 (by simp)
  · next hz =>
    have hne : ∀ u, remaining p ≠ '.' :: u := by
      intro u hu
      obtain ⟨q, hq, -⟩ := step_of_remaining hu
      exact hz q hq
    obtain ⟨rfl, rfl, rfl⟩ := Spec.frac_absent h hne
    exact ⟨_, rfl, rfl, rfl⟩
/-! ### The optional sign of an exponent -/

/--
The exponent's sign scanner consumes nothing where the next character is neither a plus nor a
minus. It is one of three cases that have to be settled before an exponent can be matched against
its derivation.

`h` names the character `c` at `p`, and `h₁` and `h₂` exclude the two signs. The conclusion is
an equality of the whole `Consumed` record: the flag `false`, the position `p` unmoved, and the
bookkeeping proof `Nat.le_refl _`. The end of the text is not covered here, `h` requiring a
character; that case is handled where the scanner's own branch on it is.
-/
theorem expSign_absent {p q : s.Pos} {c : Char} (h : step? p = some (c, q)) (h₁ : c ≠ '+')
    (h₂ : c ≠ '-') : expSign p = ⟨false, p, Nat.le_refl _⟩ := by
  rw [expSign]
  split
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with hc _
    exact absurd hc h₁
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with hc _
    exact absurd hc h₂
  · rfl

/--
The exponent's sign scanner consumes a leading plus and reports no negation. A plus is permitted
by the grammar and contributes nothing to the value, so the two readings differ only in the text
consumed.

`h : step? p = some ('+', q)` says the character is a plus. The conclusion is the whole record:
the flag `false`, the position `q` past the plus, and the bookkeeping proof drawn from `step?_lt`.
-/
theorem expSign_plus {p q : s.Pos} (h : step? p = some ('+', q)) :
    expSign p = ⟨false, q, Nat.le_of_lt (step?_lt h)⟩ := by
  rw [expSign]
  split
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with _ hq
    subst hq
    rfl
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with hc _
    exact absurd hc (by decide)
  · next h₁ _ => exact absurd h (h₁ q)

/--
The exponent's sign scanner consumes a leading minus and reports a negation. It is the one case
that changes the exponent's value, which is why the flag has to be pinned down and not only the
position.

`h : step? p = some ('-', q)` says the character is a minus. The conclusion gives the flag `true`,
the position `q` past the minus, and the bookkeeping proof drawn from `step?_lt`.
-/
theorem expSign_minus {p q : s.Pos} (h : step? p = some ('-', q)) :
    expSign p = ⟨true, q, Nat.le_of_lt (step?_lt h)⟩ := by
  rw [expSign]
  split
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with hc _
    exact absurd hc (by decide)
  · next q' hs =>
    rw [h] at hs
    injection hs with hs
    injection hs with _ hq
    subst hq
    rfl
  · next _ h₂ => exact absurd h (h₂ q)

/--
Whatever exponent a derivation read, the scanner reads, in all four of its forms. It is the widest
of the number parts, an exponent being optional and having three ways to be present.

`h` is an `Exp` derivation leaving `t`, and `hn` says `t` begins with no digit, `'e'` or `'E'`.
The conclusion produces `r` with `expPart p = .ok r`, `r.value.1 = e` and `remaining r.pos = t`;
the digit count `r.value.2` goes unmentioned, `Exp` recording none. `Spec.exp_head` under `hn`
decides which of the three present forms applies, and the three sign lemmas fix what the scanner
does with the sign in each.
-/
theorem expPart_complete {p : s.Pos} {e : Int} {t : List Char}
    (h : Spec.Exp (remaining p) e t) (hn : Spec.NoExp t) :
    ∃ r : Consumed (Int × Nat) p, expPart p = .ok r ∧ r.value.1 = e ∧ remaining r.pos = t := by
  rw [expPart]
  split
  · next c q hz =>
    have hrp := remaining_step hz
    rw [hrp] at h
    split
    · next hcond =>
      have hE : c = 'e' ∨ c = 'E' := by
        rcases Bool.or_eq_true .. ▸ hcond with h' | h'
        · exact .inl (eq_of_beq h')
        · exact .inr (eq_of_beq h')
      obtain ⟨P, v, n, hpos, hdigs, he⟩ :
          ∃ (P : s.Pos) (v n : Nat), (expSign q).pos = P ∧ Spec.Digits (remaining P) v n t ∧
            e = (if (expSign q).value then -(v : Int) else (v : Int)) := by
        rcases Spec.exp_head h hn hE with ⟨v, n, hdigs, rfl⟩ | ⟨u, v, n, hu, hdigs, rfl⟩ |
            ⟨u, v, n, hu, hdigs, rfl⟩
        · obtain ⟨d, w, hdw, hdd⟩ := Spec.digits_head hdigs
          obtain ⟨q₂, hq₂, -⟩ := step_of_remaining hdw
          rw [expSign_absent hq₂ (Spec.digit_ne hdd (by decide)) (Spec.digit_ne hdd (by decide))]
          exact ⟨q, v, n, rfl, hdigs, rfl⟩
        · obtain ⟨q₂, hq₂, hq₂u⟩ := step_of_remaining hu
          rw [expSign_plus hq₂]
          exact ⟨q₂, v, n, rfl, by rw [hq₂u]; exact hdigs, rfl⟩
        · obtain ⟨q₂, hq₂, hq₂u⟩ := step_of_remaining hu
          rw [expSign_minus hq₂]
          exact ⟨q₂, v, n, rfl, by rw [hq₂u]; exact hdigs, rfl⟩
      split
      · next negative r hsign heq =>
        simp only [heq] at hpos he
        subst hpos
        obtain ⟨d, w, hdw, hdd⟩ := Spec.digits_head hdigs
        obtain ⟨q₃, hq₃, -⟩ := step_of_remaining hdw
        split
        · next d' r'' hd2 =>
          have hqq := hq₃.symm.trans hd2
          simp only [Option.some.injEq, Prod.mk.injEq] at hqq
          obtain ⟨rfl, rfl⟩ := hqq
          split
          · next hdig =>
            obtain ⟨hval, hrest⟩ := digits_complete hq₃ hdig hdigs (Spec.noDigit_of_noExp hn)
            refine ⟨_, rfl, ?_, hrest⟩
            simp only [hval, he]
          · next hdig => exact absurd hdd hdig
        · next hd2 => rw [hq₃] at hd2; exact absurd hd2 (by simp)
    · next hcond =>
      have hne : ∀ c' u, c :: remaining q = c' :: u → c' ≠ 'e' ∧ c' ≠ 'E' := by
        intro c' u hu
        injection hu with hcc
        subst hcc
        exact ⟨fun hE => hcond (by simp [hE]), fun hE => hcond (by simp [hE])⟩
      obtain ⟨rfl, rfl⟩ := Spec.exp_absent h hne
      exact ⟨_, rfl, rfl, hrp⟩
  · next hz =>
    rw [remaining_none hz] at h
    obtain ⟨rfl, rfl⟩ := Spec.exp_absent h (by intro c u hu; exact absurd hu (by simp))
    exact ⟨_, rfl, rfl, remaining_none hz⟩

/--
The four parts of a number, once the sign is known, are read by the scanner exactly as the
derivation read them. Factoring the sign out lets one proof serve both branches of `number`, as it
does in the soundness direction.

`hi`, `hfr` and `hex` are the integer, fraction and exponent derivations threaded through `u₂`
and `u₃`, and `hft` says the number has ended, which is what supplies each part's maximality
condition through `noDigit_after_int`, `noFrac_after_exp` and `noExp_of_follows`. `hlim` turns the
digit limit off, without which a long significand would be refused and the scan would fail. The
conclusion produces the result, its value written as the grammar computes it, and its stopping
position.
-/
theorem unsignedNumber_complete {cfg : Config} {p : s.Pos} {neg : Bool} {i f nf : Nat} {e : Int}
    {u₂ u₃ t : List Char} (hi : Spec.Int' (remaining p) i u₂) (hfr : Spec.Frac u₂ f nf u₃)
    (hex : Spec.Exp u₃ e t) (hft : Spec.Follows t) (hlim : cfg.maxNumberDigits = none) :
    ∃ r : Scanned Number p, unsignedNumber cfg p neg = .ok r ∧
      r.value = Number.normalize
        (if neg then -((i * 10 ^ nf + f : Nat) : Int) else ((i * 10 ^ nf + f : Nat) : Int))
        (e - nf) ∧ remaining r.pos = t := by
  obtain ⟨ri, hri, hriv, hrip⟩ := intPart_complete hi (Spec.noDigit_after_int hfr hex hft)
  rw [← hrip] at hfr
  obtain ⟨rf, hrf, hrfv, hrfp⟩ := fracPart_complete hfr (Spec.noFrac_after_exp hex hft)
  rw [← hrfp] at hex
  obtain ⟨rx, hrx, hrxv, hrxp⟩ := expPart_complete hex (Spec.noExp_of_follows hft)
  simp only [unsignedNumber, hri, hrf, hrx, tooManyDigits, hlim, Bool.or_self]
  refine ⟨_, rfl, ?_, hrxp⟩
  simp only [hriv, hrfv, hrxv]

/--
Whatever number a derivation read, the scanner reads, returning the same value and stopping in the
same place. It is where the number half of completeness is finished.

`h` is a `Num` derivation leaving `t`, `hft` says the number has ended there, and `hlim` turns the
digit limit off. The conclusion produces `r` with `number cfg p = .ok r`, `r.value = n` and
`remaining r.pos = t`. `Spec.sign_head` decides which of the scanner's branches applies; its third
branch, the end of the text, cannot arise, `Int'` requiring a character.
-/
theorem number_complete {cfg : Config} {p : s.Pos} {n : Number} {t : List Char}
    (h : Spec.Num (remaining p) n t) (hft : Spec.Follows t) (hlim : cfg.maxNumberDigits = none) :
    ∃ r : Scanned Number p, number cfg p = .ok r ∧ r.value = n ∧ remaining r.pos = t := by
  cases h with
  | mk hs hi hfr hex =>
    rw [number]
    split
    · next q hz =>
      rcases Spec.sign_head hs with ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
      · obtain ⟨c, u, hcu, hd⟩ := Spec.int_head hi
        rw [remaining_step hz] at hcu
        injection hcu with hcc
        subst hcc
        exact absurd hd (by decide)
      · rw [remaining_step hz] at hm
        injection hm with _ hst
        rw [← hst] at hi
        obtain ⟨ru, hru, hruv, hrup⟩ := unsignedNumber_complete hi hfr hex hft hlim
        rw [hru]
        exact ⟨_, rfl, hruv, hrup⟩
    · next q hne hz =>
      rcases Spec.sign_head hs with ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
      · obtain ⟨ru, hru, hruv, hrup⟩ := unsignedNumber_complete hi hfr hex hft hlim
        rw [hru]
        exact ⟨_, rfl, hruv, hrup⟩
      · rw [remaining_step hz] at hm
        injection hm with hcc
        exact absurd (by rw [← hcc] : q = ('-', q.snd)) (hne q.snd)
    · next hz =>
      obtain ⟨c, u, hcu, -⟩ := Spec.int_head hi
      rcases Spec.sign_head hs with ⟨rfl, rfl⟩ | ⟨rfl, hm⟩
      · rw [remaining_none hz] at hcu
        exact absurd hcu (by simp)
      · rw [remaining_none hz] at hm
        exact absurd hm (by simp)

/-! ## Strings -/

/--
A character's own code point builds that character back. The `\u` escapes are matched by number,
so the construction has to be shown to invert what `toNat` reads off.

`charOfCodePoint? c.toNat = some c` says the construction succeeds and returns `c` itself, not
merely a character with the same code point. Its validity check is discharged by `c.valid`, which
every `Char` carries, so the `none` branch cannot be reached from a code point that came from a
character.
-/
theorem charOfCodePoint?_self (c : Char) : charOfCodePoint? c.toNat = some c := by
  have hv : UInt32.ofNat c.toNat = c.val := UInt32.ofNat_toNat
  rw [charOfCodePoint?, dite_eq_left (hv ▸ c.valid)]
  simp [hv]

/--
Whatever hexadecimal digit a derivation read, the scanner reads. `Hex4` is stated through
`hexVal?` and the scanner tests that same function, so the two agree once the character is known.

`hl` says the text at `p` begins with `c` and `hv` says `c` is a hexadecimal digit of value `v`.
The conclusion produces `r` with `hexDigit? p = some r`, `r.value = v` and `remaining r.pos = t`,
so exactly one character is consumed and the value matches.
-/
theorem hexDigit?_complete {p : s.Pos} {c : Char} {v : Nat} {t : List Char}
    (hl : remaining p = c :: t) (hv : Spec.hexVal? c = some v) :
    ∃ r : Scanned Nat p, hexDigit? p = some r ∧ r.value = v ∧ remaining r.pos = t := by
  obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
  rw [hexDigit?]
  split
  · next c' q' hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with hcc hqq
    subst hcc
    subst hqq
    split
    · next v' hv' =>
      rw [hv] at hv'
      injection hv' with hvv
      exact ⟨_, rfl, hvv.symm, hqt⟩
    · next hv' => rw [hv] at hv'; exact absurd hv' (by simp)
  · next hc => rw [hq] at hc; exact absurd hc (by simp)

/--
Whatever four hexadecimal digits a derivation read, the scanner reads, computing the same value.
It is the body of a `\u` escape, so both of the escape rules go through it.

`hl` identifies the text at `p` with the derivation's `l`, and `h` is the `Hex4` derivation. The
conclusion produces `r` with `hex4? p = some r`, `r.value = v` and `remaining r.pos = t`. The
single constructor yields four `hexVal?` facts, each fed to `hexDigit?_complete` at the position
the previous one left.
-/
theorem hex4?_complete {p : s.Pos} {l : List Char} {v : Nat} {t : List Char}
    (hl : remaining p = l) (h : Spec.Hex4 l v t) :
    ∃ r : Scanned Nat p, hex4? p = some r ∧ r.value = v ∧ remaining r.pos = t := by
  cases h with
  | mk h₁ h₂ h₃ h₄ =>
    obtain ⟨r₁, hr₁, hv₁, hp₁⟩ := hexDigit?_complete hl h₁
    obtain ⟨r₂, hr₂, hv₂, hp₂⟩ := hexDigit?_complete hp₁ h₂
    obtain ⟨r₃, hr₃, hv₃, hp₃⟩ := hexDigit?_complete hp₂ h₃
    obtain ⟨r₄, hr₄, hv₄, hp₄⟩ := hexDigit?_complete hp₃ h₄
    simp only [hex4?, hr₁, hr₂, hr₃, hr₄]
    exact ⟨_, rfl, by rw [hv₁, hv₂, hv₃, hv₄], hp₄⟩

/--
Whatever `\uXXXX` escape a derivation read, the scanner reads. The surrogate-pair rule names the
backslash and the `u` of the second escape explicitly, so the scanner's combined lookahead has to
be matched to that shape.

`hl` says the text at `p` is `'\\'`, then `'u'`, then `l`, and `h` is a `Hex4` derivation from
`l`. The conclusion produces `r` with `escapeHex4? p = some r`, `r.value = v` and
`remaining r.pos = t`. The two leading characters are consumed through `step_of_remaining` before
`hex4?_complete` is applied to the rest.
-/
theorem escapeHex4?_complete {p : s.Pos} {l : List Char} {v : Nat} {t : List Char}
    (hl : remaining p = '\\' :: 'u' :: l) (h : Spec.Hex4 l v t) :
    ∃ r : Scanned Nat p, escapeHex4? p = some r ∧ r.value = v ∧ remaining r.pos = t := by
  obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
  obtain ⟨w, hw, hwt⟩ := step_of_remaining hqt
  obtain ⟨r, hr, hrv, hrp⟩ := hex4?_complete hwt h
  rw [escapeHex4?]
  split
  · next q' hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with _ hqq
    subst hqq
    split
    · next w' hu =>
      rw [hw] at hu
      injection hu with hu'
      injection hu' with _ hww
      subst hww
      rw [hr]
      exact ⟨_, rfl, hrv, hrp⟩
    · next hu => exact (hu w hw).elim
  · next hc => exact (hc q hq).elim

/--
An unescaped character is read as itself. It is the commonest case by far, and the only one that
consumes a single character.

`hs` says `c` is the character at `p` and `hu` says it satisfies `isUnescaped`. The conclusion
`stringStep p = .char c q` fixes the machine's answer exactly. The earlier branches, which test
for `'"'` and `'\\'`, are excluded because `isUnescaped` holds of neither.
-/
theorem stringStep_unescaped {p q : s.Pos} {c : Char} (hs : step? p = some (c, q))
    (hu : Spec.isUnescaped c = true) : stringStep p = .char c q := by
  rw [stringStep]
  split
  · next hc => rw [hs] at hc; exact absurd hc (by simp)
  · next w hc =>
    rw [hs] at hc
    injection hc with hc'
    injection hc' with hcc
    rw [hcc] at hu
    exact absurd hu (by decide)
  · next w hc =>
    rw [hs] at hc
    injection hc with hc'
    injection hc' with hcc
    rw [hcc] at hu
    exact absurd hu (by decide)
  · next c' w hc =>
    rw [hs] at hc
    injection hc with hc'
    injection hc' with hcc hww
    subst hcc
    subst hww
    rw [ite_eq_left hu]

/--
A two-character escape is read as the character it stands for. There are eight of them and the
scanner disposes of all eight through one function, so one lemma covers them together.

`h₁` and `h₂` say the text is a backslash followed by `d`, and `he` says
`escapeChar? d = some ch`. The conclusion `stringStep p = .char ch r` consumes both characters.
That `d` is not `'u'` follows from `he`, `escapeChar?` answering `none` there, and it is what
keeps this case out of the `\u` branch.
-/
theorem stringStep_escape {p q r : s.Pos} {d ch : Char} (h₁ : step? p = some ('\\', q))
    (h₂ : step? q = some (d, r)) (he : escapeChar? d = some ch) : stringStep p = .char ch r := by
  have hu : d ≠ 'u' := by intro h; rw [h] at he; simp [escapeChar?] at he
  rw [stringStep]
  split
  · next hc => rw [h₁] at hc; exact absurd hc (by simp)
  · next w hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact absurd hcc (by decide)
  · next w hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with _ hww
    subst hww
    split
    · next hd => rw [h₂] at hd; exact absurd hd (by simp)
    · next w' hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with hdd
      exact absurd hdd hu
    · next d' w' hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with hdd hww'
      subst hdd
      subst hww'
      rw [he]
  · next _ _ _ _ hn2 hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact (hn2 hcc.symm).elim

/--
A `\u` escape naming a character outside the surrogate range is read as that character. The
scanner tests the range and the grammar does not, so the two are reconciled by no `Char` carrying
a surrogate code point.

`h₁` and `h₂` say the text begins `\u`, `hx` is the `Hex4` derivation, and `hcv` says the
character's code point is the value read. The conclusion produces the position after the escape,
with `stringStep p = .char c r` and `remaining r = t`. `Spec.char_not_surrogate` is what
discharges the scanner's range test, and `charOfCodePoint?_self` what makes the construction
return `c`.
-/
theorem stringStep_codePoint {p q w : s.Pos} {v : Nat} {t : List Char} {c : Char}
    (h₁ : step? p = some ('\\', q)) (h₂ : step? q = some ('u', w))
    (hx : Spec.Hex4 (remaining w) v t) (hcv : c.toNat = v) :
    ∃ r : s.Pos, stringStep p = .char c r ∧ remaining r = t := by
  obtain ⟨h4, hh4, hh4v, hh4p⟩ := hex4?_complete rfl hx
  rw [stringStep]
  split
  · next hc => rw [h₁] at hc; exact absurd hc (by simp)
  · next w' hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact absurd hcc (by decide)
  · next w' hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with _ hww
    subst hww
    split
    · next hd => rw [h₂] at hd; exact absurd hd (by simp)
    · next w'' hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with _ hww2
      subst hww2
      simp only [hh4]
      have hcond : (decide (h4.value < 0xD800) || decide (0xDFFF < h4.value)) = true := by
        rw [hh4v, ← hcv]
        rcases Spec.char_not_surrogate c with hs | hs
        · simp [hs]
        · simp [hs]
      rw [ite_eq_left hcond, hh4v, ← hcv, charOfCodePoint?_self]
      exact ⟨_, rfl, hh4p⟩
    · next _ _ _ hn hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with hdd
      exact (hn hdd.symm).elim
  · next _ _ _ _ hn2 hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact (hn2 hcc.symm).elim

/--
A pair of `\u` escapes naming a high and a low surrogate is read as the character they combine to.
It is the only case in which one character costs twelve, and the only one in which the scanner
looks ahead past a complete escape.

`h₁` and `h₂` open the first escape, `hx₁` derives the high half and leaves a text beginning
with a second `\u`, and `hx₂` derives the low half from it. The four bounds place `hi` and `lo`
inside their surrogate blocks, which is what discharges the scanner's own range tests, and `hcv`
gives the combined code point. The conclusion produces the position after both escapes;
`charOfCodePoint?_self` is again what makes the construction return `c` rather than some other
character of the same number.
-/
theorem stringStep_surrogate {p q w : s.Pos} {s₂ t : List Char} {hi lo : Nat} {c : Char}
    (h₁ : step? p = some ('\\', q)) (h₂ : step? q = some ('u', w))
    (hx₁ : Spec.Hex4 (remaining w) hi ('\\' :: 'u' :: s₂)) (hx₂ : Spec.Hex4 s₂ lo t)
    (hhi₁ : 0xD800 ≤ hi) (hhi₂ : hi ≤ 0xDBFF) (hlo₁ : 0xDC00 ≤ lo) (hlo₂ : lo ≤ 0xDFFF)
    (hcv : c.toNat = 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)) :
    ∃ r : s.Pos, stringStep p = .char c r ∧ remaining r = t := by
  obtain ⟨h4, hh4, hh4v, hh4p⟩ := hex4?_complete rfl hx₁
  obtain ⟨l4, hl4, hl4v, hl4p⟩ := escapeHex4?_complete hh4p hx₂
  rw [stringStep]
  split
  · next hc => rw [h₁] at hc; exact absurd hc (by simp)
  · next w' hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact absurd hcc (by decide)
  · next w' hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with _ hww
    subst hww
    split
    · next hd => rw [h₂] at hd; exact absurd hd (by simp)
    · next w'' hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with _ hww2
      subst hww2
      simp only [hh4]
      have hhigh : ¬((decide (h4.value < 0xD800) || decide (0xDFFF < h4.value)) = true) := by
        rw [hh4v]
        simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt]
        omega
      rw [ite_eq_right hhigh, ite_eq_left (show h4.value ≤ 0xDBFF by rw [hh4v]; omega)]
      simp only [hl4]
      rw [ite_eq_left (show (decide (0xDC00 ≤ l4.value) && decide (l4.value ≤ 0xDFFF)) = true by
        rw [hl4v]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
      have hcomb : combineSurrogates h4.value l4.value = c.toNat := by
        rw [hh4v, hl4v, hcv]
        rfl
      rw [hcomb, charOfCodePoint?_self]
      exact ⟨_, rfl, hl4p⟩
    · next _ _ _ hn hd =>
      rw [h₂] at hd
      injection hd with hd'
      injection hd' with hdd
      exact (hn hdd.symm).elim
  · next _ _ _ _ hn2 hc =>
    rw [h₁] at hc
    injection hc with hc'
    injection hc' with hcc
    exact (hn2 hcc.symm).elim

/--
Whatever character of a string literal a derivation read, the machine reads. It gathers the four
cases above into the single form the string loop needs.

`hl` identifies the text at `p` with the derivation's `l`, and `h` is the `Ch` derivation. The
conclusion produces the position `q` with `stringStep p = .char c q` and `remaining q = t`. The
eleven constructors of `Ch` reduce to four scanner cases, the eight short escapes sharing one
through `escapeChar?`.
-/
theorem stringStep_char_complete {p : s.Pos} {l : List Char} {c : Char} {t : List Char}
    (hl : remaining p = l) (h : Spec.Ch l c t) :
    ∃ q, stringStep p = .char c q ∧ remaining q = t := by
  cases h with
  | unescaped hu =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
    exact ⟨q, stringStep_unescaped hq hu, hqt⟩
  | quote | backslash | solidus | backspace | formFeed | lineFeed | carriageReturn | tab =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
    obtain ⟨r, hr, hrt⟩ := step_of_remaining hqt
    exact ⟨r, stringStep_escape hq hr (by decide), hrt⟩
  | codePoint hx hcv =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
    obtain ⟨w, hw, hwt⟩ := step_of_remaining hqt
    exact stringStep_codePoint hq hw (by rw [hwt]; exact hx) hcv
  | surrogatePair hx₁ hx₂ ha hb hc hd hcv =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
    obtain ⟨w, hw, hwt⟩ := step_of_remaining hqt
    exact stringStep_surrogate hq hw (by rw [hwt]; exact hx₁) hx₂ ha hb hc hd hcv

/--
A closing quotation mark is read as the end of the literal. The body's derivation stops there, and
the machine has to be shown to stop there too rather than read the quote as another character.

`hl` says the text at `p` begins with `'"'`. The conclusion produces `q` with
`stringStep p = .done q` and `remaining q = t`. The unescaped branch is what has to be excluded,
and `isUnescaped '"'` being false is what excludes it.
-/
theorem stringStep_done_complete {p : s.Pos} {t : List Char} (hl : remaining p = '"' :: t) :
    ∃ q, stringStep p = .done q ∧ remaining q = t := by
  obtain ⟨q, hq, hqt⟩ := step_of_remaining hl
  refine ⟨q, ?_, hqt⟩
  rw [stringStep]
  split
  · next hc => rw [hq] at hc; exact absurd hc (by simp)
  · next w hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with _ hww
    rw [hww]
  · next w hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with hcc
    exact absurd hcc (by decide)
  · next _ _ _ hn1 _ hc =>
    rw [hq] at hc
    injection hc with hc'
    injection hc' with hcc
    exact (hn1 hcc.symm).elim

/--
The string loop, from any point inside a literal's body, reads whatever run of characters the
derivation read and stops at the closing quote. The loop carries an accumulator, so the claim can
only serve as an induction hypothesis with that accumulator left free.

`h : Spec.Chars l cs r` is the derivation, `p` the position, `acc` what has been built so far, and
the two equations say the text at `p` is `l` and that `r` begins with the closing quote. The
conclusion produces the result with `string.go start p acc hp = .ok res`, its characters being
`acc` followed by `cs`, and its position leaving `t`. The induction is on the derivation rather
than on the text, `Chars` being a plain inductive and not part of the mutual value family.
-/
private theorem string_go_complete {start : s.Pos} {l cs r : List Char} (h : Spec.Chars l cs r) :
    ∀ (p : s.Pos) (acc : String) (hp : p.remainingBytes ≤ start.remainingBytes) (t : List Char),
      remaining p = l → r = '"' :: t →
      ∃ res : Scanned String start, string.go start p acc hp = .ok res ∧
        res.value.toList = acc.toList ++ cs ∧ remaining res.pos = t := by
  induction h with
  | nil =>
    intro p acc hp t hpl hr
    obtain ⟨q, hq, hqt⟩ := stringStep_done_complete (by rw [hpl, hr])
    rw [string.go]
    split
    · next e hs => rw [hq] at hs; exact absurd hs (by simp)
    · next q' hs =>
      rw [hq] at hs
      injection hs with hqq
      subst hqq
      exact ⟨_, rfl, by simp, hqt⟩
    · next c q' hs => rw [hq] at hs; exact absurd hs (by simp)
  | @cons _ _ _ ch _ hch _ ih =>
    intro p acc hp t hpl hr
    obtain ⟨q, hq, hqt⟩ := stringStep_char_complete hpl hch
    rw [string.go]
    split
    · next e hs => rw [hq] at hs; exact absurd hs (by simp)
    · next q' hs => rw [hq] at hs; exact absurd hs (by simp)
    · next c' q' hs =>
      rw [hq] at hs
      injection hs with hcc hqq
      subst hcc
      subst hqq
      obtain ⟨res, hres, hval, hpos⟩ := ih q (acc.push ch) _ t hqt hr
      exact ⟨res, hres, by rw [hval, String.toList_push]; simp, hpos⟩

/--
Whatever body a derivation read between quotation marks, the scanner reads. It is the loop's claim
taken at the point the machine enters it.

`h` is a `Chars` derivation from the text at `p` whose remainder begins with the closing quote.
The conclusion produces `res` with `string p acc = .ok res`, `res.value.toList = acc.toList ++ cs`
and `remaining res.pos = t`. It is `string_go_complete` at the loop's starting position, where the
bookkeeping bound is reflexivity.
-/
theorem string_complete {p : s.Pos} {acc : String} {cs t : List Char}
    (h : Spec.Chars (remaining p) cs ('"' :: t)) :
    ∃ res : Scanned String p, string p acc = .ok res ∧
      res.value.toList = acc.toList ++ cs ∧ remaining res.pos = t :=
  string_go_complete h p acc (Nat.le_refl _) t rfl rfl

/--
Whatever string literal a derivation read, the scanner reads, returning the same string. Both
quotation marks are accounted for, which is what lets the value machine and the member reader both
use it.

`hl` identifies the text at `p` with the derivation's `l`, and `h` is the `Str` derivation. The
conclusion produces both the position `q` after the opening quote and the scan result, with
`step? p = some ('"', q)`, `string q "" = .ok res`, `res.value = v` and `remaining res.pos = t`.
`String.ofList_toList` is what makes the returned string the very one the derivation named rather
than one merely equal to it character by character.
-/
theorem str_complete {p : s.Pos} {l : List Char} {v : String} {t : List Char}
    (hl : remaining p = l) (h : Spec.Str l v t) :
    ∃ (q : s.Pos) (res : Scanned String q), step? p = some ('"', q) ∧ string q "" = .ok res ∧
      res.value = v ∧ remaining res.pos = t := by
  cases h with
  | @mk u cs r hchars =>
    obtain ⟨q, hq, hqu⟩ := step_of_remaining hl
    obtain ⟨res, hres, hval, hpos⟩ := string_complete (acc := "") (by rw [hqu]; exact hchars)
    refine ⟨q, res, hq, hres, ?_, hpos⟩
    have hcs : res.value.toList = cs := by simpa using hval
    rw [← hcs, String.ofList_toList]

/-! ## The machine -/

/--
Where a derivation begins with a fixed list of characters, the scanner matches them. The three
literals are read this way, and this is what turns each of their derivations into a successful
scan.

`h : remaining p = l ++ u` says the text at `p` begins with `l`. The conclusion produces `r` with
`expect? p l = some r` and `remaining r.pos = u`. The induction is on `l`, generalising `p`, each
character being matched at a fresh position.
-/
theorem expect?_complete {p : s.Pos} {l u : List Char} (h : remaining p = l ++ u) :
    ∃ r : Consumed Unit p, expect? p l = some r ∧ remaining r.pos = u := by
  induction l generalizing p with
  | nil => exact ⟨_, rfl, by simpa using h⟩
  | cons c rest ih =>
    obtain ⟨q, hq, hqt⟩ := step_of_remaining (by simpa using h)
    obtain ⟨r, hr, hrp⟩ := ih hqt
    rw [expect?]
    split
    · next c' q' hc =>
      rw [hq] at hc
      injection hc with hc'
      injection hc' with hcc hqq
      subst hcc
      subst hqq
      rw [ite_eq_left (beq_self_eq_true c), hr]
      exact ⟨_, rfl, hrp⟩
    · next hc => rw [hq] at hc; exact absurd hc (by simp)

/-!
The elements and members of a container come apart into a first and a rest, which is the shape
the machine reads them in. The value family is one mutual definition, so the induction is on how
much text is left rather than on the derivation.
-/

/--
An array's elements come apart into the first and the rest, at any length of text. The machine
reads one element and defers the remainder, so the derivation has to be split the same way; the
value family is one mutual definition, so the induction runs on the length rather than on the
derivation.

`n` bounds the text's length, by `t.length ≤ n`. Given an `Elements` derivation and the
`EndArray` after it, the conclusion produces the first value `v`, the remaining values `vs'`, the
text `t₁` between them, a `Value` derivation for the first and an `ElementsRest` for what
follows. The bound cannot empty the claim, `n := t.length` satisfying it for every `t`.
-/
private theorem elementsEnd_uncons_go : ∀ (n : Nat) (t : List Char), t.length ≤ n →
    ∀ {t' r : List Char} {vs : List Json}, Spec.Elements t vs t' → Spec.EndArray t' r →
      ∃ (v : Json) (vs' : List Json) (t₁ : List Char), vs = v :: vs' ∧ Spec.Value t v t₁ ∧
        ElementsRest t₁ vs' r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t ht t' r vs h hend
    cases h with
    | one hv => exact ⟨_, [], _, rfl, hv, ElementsRest.close hend⟩
    | @more _ _ s'' _ _ _ hv hsep hels =>
      have hlt : s''.length < n := by
        have h₁ := Spec.value_length hv
        have h₂ := Spec.token_length hsep
        omega
      obtain ⟨v₂, vs₂, t₂, rfl, hv₂, hrest⟩ := ih _ hlt _ (Nat.le_refl _) hels hend
      exact ⟨_, _, _, rfl, hv, ElementsRest.more hsep hv₂ hrest⟩

/--
An object's members come apart into the first and the rest, at any length of text. It is the
object counterpart of the array split, needed separately because `Members` is a distinct
production over differently shaped contents.

`n` bounds the text's length. Given a `Members` derivation and the `EndObject` after it, the
conclusion produces the first member, the remaining members, the text between them, a `Member`
derivation for the first and a `MembersRest` for the rest. As before the bound is met at
`n := t.length`, so it excludes nothing.
-/
private theorem membersEnd_uncons_go : ∀ (n : Nat) (t : List Char), t.length ≤ n →
    ∀ {t' r : List Char} {ms : List (String × Json)}, Spec.Members t ms t' →
      Spec.EndObject t' r →
      ∃ (m : String × Json) (ms' : List (String × Json)) (t₁ : List Char), ms = m :: ms' ∧
        Spec.Member t m t₁ ∧ MembersRest t₁ ms' r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro t ht t' r ms h hend
    cases h with
    | one hm => exact ⟨_, [], _, rfl, hm, MembersRest.close hend⟩
    | @more _ _ s'' _ _ _ hm hsep hms =>
      have hlt : s''.length < n := by
        have h₁ := Spec.member_length hm
        have h₂ := Spec.token_length hsep
        omega
      obtain ⟨m₂, ms₂, t₂, rfl, hm₂, hrest⟩ := ih _ hlt _ (Nat.le_refl _) hms hend
      exact ⟨_, _, _, rfl, hm, MembersRest.more hsep hm₂ hrest⟩

/--
An array's elements split into the first and what has to follow it. This is the shape the machine
reads them in, one value at a time with the rest of the array still outstanding, so it is what
lets the completeness induction be driven by the derivation.

`h` is the `Elements` derivation and `hend` the closing bracket after it. The conclusion produces
the first value, the rest, the text between them, the `Value` derivation and the `ElementsRest`.
It is the general form taken at `n := t.length`.
-/
theorem elementsEnd_uncons {t t' r : List Char} {vs : List Json} (h : Spec.Elements t vs t')
    (hend : Spec.EndArray t' r) :
    ∃ (v : Json) (vs' : List Json) (t₁ : List Char), vs = v :: vs' ∧ Spec.Value t v t₁ ∧
      ElementsRest t₁ vs' r :=
  elementsEnd_uncons_go t.length t (Nat.le_refl _) h hend

/--
An object's members split into the first and what has to follow it. It is what the machine's
member reader needs: one member in hand, and everything after it recorded as an obligation.

`h` is the `Members` derivation and `hend` the closing brace after it. The conclusion produces the
first member, the rest, the text between them, the `Member` derivation and the `MembersRest`. It
is the general form taken at `n := t.length`.
-/
theorem membersEnd_uncons {t t' r : List Char} {ms : List (String × Json)}
    (h : Spec.Members t ms t') (hend : Spec.EndObject t' r) :
    ∃ (m : String × Json) (ms' : List (String × Json)) (t₁ : List Char), ms = m :: ms' ∧
      Spec.Member t m t₁ ∧ MembersRest t₁ ms' r :=
  membersEnd_uncons_go t.length t (Nat.le_refl _) h hend

/-!
The machine reads by looking at one character and dispatching on it. Each of the lemmas below
says what it does once that character is known, so that the induction can be driven by the
derivation rather than by the parser.
-/

variable {cfg : Config} {depth : Nat} {stack : List Frame}

/--
Seeing an `n` followed by `ull`, the machine reads `null` and hands it on. Each of these lemmas
says what the machine does once its leading character is known, so that the induction can be
driven by the derivation rather than by the parser's own case analysis.

`hc` says the character at `p` is `'n'` and `hex` says the three characters after it are `ull`.
The conclusion equates the whole call with `continueWith` on `Json.null` at the position the
literal ended. The other branches of `value` are excluded by the leading character alone.
-/
private theorem value_null {p q : s.Pos} {e : Consumed Unit q} (hc : step? p = some ('n', q))
    (hex : expect? q ['u', 'l', 'l'] = some e) :
    value cfg p depth stack = continueWith cfg .null e.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    rw [hex]
  · rename_i hn _ _ _ _ _
    exact absurd heq.1.symm hn

/--
Seeing a `t` followed by `rue`, the machine reads `true` and hands it on. It is one of three
literal branches, all dispatched on a single character and all needing their own lemma, the
expected characters differing.

`hc` says the character at `p` is `'t'` and `hex` says the three after it are `rue`. The
conclusion equates the call with `continueWith` on `.bool true` at the position the literal ended.
-/
private theorem value_true {p q : s.Pos} {e : Consumed Unit q} (hc : step? p = some ('t', q))
    (hex : expect? q ['r', 'u', 'e'] = some e) :
    value cfg p depth stack = continueWith cfg (.bool true) e.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    rw [hex]
  · rename_i _ hn _ _ _ _
    exact absurd heq.1.symm hn

/--
Seeing an `f` followed by `alse`, the machine reads `false` and hands it on. It is the longest of
the three literals, and the only one of five characters, which is why its expected list differs.

`hc` says the character at `p` is `'f'` and `hex` says the four after it are `alse`. The
conclusion equates the call with `continueWith` on `.bool false` at the position the literal
ended.
-/
private theorem value_false {p q : s.Pos} {e : Consumed Unit q} (hc : step? p = some ('f', q))
    (hex : expect? q ['a', 'l', 's', 'e'] = some e) :
    value cfg p depth stack = continueWith cfg (.bool false) e.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    rw [hex]
  · rename_i _ _ hn _ _ _
    exact absurd heq.1.symm hn

/--
Seeing a quotation mark, the machine reads a string and hands it on. The dispatch is the same as
for the literals, but the value comes from a scan rather than from a fixed list of characters.

`hc` says the character at `p` is `'"'` and `hstr` says the body scanned to `r`. The conclusion
equates the call with `continueWith` on `.str r.value` at `r.pos`, so both the value read and the
position reached are those the scan reports.
-/
private theorem value_str {p q : s.Pos} {r : Scanned String q} (hc : step? p = some ('"', q))
    (hstr : string q "" = .ok r) :
    value cfg p depth stack = continueWith cfg (.str r.value) r.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    rw [hstr]
  · rename_i _ _ _ hn _ _
    exact absurd heq.1.symm hn

/--
Seeing a minus or a digit, the machine reads a number and hands it on. It is the last branch of
the dispatch, reached only when the leading character is none of the others.

`hc` names the character `c`, `hd` says it is a minus or a digit, and `hnum` says the number
scanned to `r`. The conclusion equates the call with `continueWith` on `.num r.value` at `r.pos`.
The six earlier branches are excluded by `hd`, each of their leading characters being neither a
minus nor a digit.
-/
private theorem value_num {p q : s.Pos} {c : Char} {r : Scanned Number p}
    (hc : step? p = some (c, q)) (hd : (c == '-' || Spec.isDigit c) = true)
    (hnum : number cfg p = .ok r) :
    value cfg p depth stack = continueWith cfg (.num r.value) r.pos depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    exact absurd hd (by decide)
  · obtain ⟨rfl, -⟩ := heq
    rw [ite_eq_left hd, hnum]

/--
Seeing `[` and then `]`, the machine produces the empty array without opening a frame. The empty
container is the one case that does not descend, so it has to be separated from the general one.

`hc` says the character at `p` is `'['`, `hd` says the depth limit is not exceeded, and `hb` says
the first character after the whitespace is `']'`. The conclusion equates the call with
`continueWith` on `.arr #[]` at the position after that bracket. `hd` is what keeps the call out
of the depth-exceeded branch, where it would return an error instead.
-/
private theorem value_arr_empty {p q after : s.Pos} (hc : step? p = some ('[', q))
    (hd : depthExceeded cfg depth = false) (hb : step? (skipWs q).pos = some (']', after)) :
    value cfg p depth stack = continueWith cfg (.arr #[]) after depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hd, Bool.false_eq_true, ite_false]
    split <;> rename_i heq2 <;> rw [hb] at heq2 <;> simp at heq2
    · subst heq2
      rfl
  · rename_i _ _ _ _ hn _
    exact absurd heq.1.symm hn

/--
Seeing `[` and then anything but `]`, the machine opens an array frame and reads the first
element. It is the descending case, and where the depth counter is increased.

`hc` says the character is `'['`, `hd` says the depth limit is not exceeded, and `hb` says no
`']'` follows the whitespace. The conclusion equates the call with `value` at the position after
that whitespace, at a depth one greater and with an empty array frame pushed onto the stack.
-/
private theorem value_arr_items {p q : s.Pos} (hc : step? p = some ('[', q))
    (hd : depthExceeded cfg depth = false)
    (hb : ∀ after, step? (skipWs q).pos ≠ some (']', after)) :
    value cfg p depth stack = value cfg (skipWs q).pos (depth + 1) (.arr #[] :: stack) := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hd, Bool.false_eq_true, ite_false]
  · rename_i _ _ _ _ hn _
    exact absurd heq.1.symm hn

/--
Seeing `{` and then `}`, the machine produces the empty object without opening a frame. As with
the empty array it is the case that does not descend, and it needs its own lemma, the characters
and the value both differing.

`hc` says the character at `p` is `'{'`, `hd` says the depth limit is not exceeded, and `hb` says
the first character after the whitespace is `'}'`. The conclusion equates the call with
`continueWith` on `.obj #[]` at the position after that brace.
-/
private theorem value_obj_empty {p q after : s.Pos} (hc : step? p = some ('{', q))
    (hd : depthExceeded cfg depth = false) (hb : step? (skipWs q).pos = some ('}', after)) :
    value cfg p depth stack = continueWith cfg (.obj #[]) after depth stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hd, Bool.false_eq_true, ite_false]
    split <;> rename_i heq2 <;> rw [hb] at heq2 <;> simp at heq2
    · subst heq2
      rfl
  · rename_i _ _ _ _ _ hn
    exact absurd heq.1.symm hn

/--
Seeing `{` and then anything but `}`, the machine opens an object frame and reads the first
member. Unlike the array case it does not call `value` next but `member`, an object's contents
beginning with a name rather than a value.

`hc` says the character is `'{'`, `hd` says the depth limit is not exceeded, and `hb` says no
`'}'` follows the whitespace. The conclusion equates the call with `member` at the position after
that whitespace, at a depth one greater, with empty fields and an empty set of names seen.
-/
private theorem value_obj_members {p q : s.Pos} (hc : step? p = some ('{', q))
    (hd : depthExceeded cfg depth = false)
    (hb : ∀ after, step? (skipWs q).pos ≠ some ('}', after)) :
    value cfg p depth stack = member cfg (skipWs q).pos (depth + 1) #[] ∅ stack := by
  rw [value]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hd, Bool.false_eq_true, ite_false]
  · rename_i _ _ _ _ _ hn
    exact absurd heq.1.symm hn

/--
With no frame waiting, a completed value is the answer. It is where the machine stops, and where
the value returned is finally identified with the value read.

`continueWith cfg v p depth [] = .ok (v, p)` returns both the value and the position untouched. It
holds by unfolding alone, for every configuration, depth and position, no scanning being done in
this case at all.
-/
private theorem continueWith_nil {p : s.Pos} {v : Json} :
    continueWith cfg v p depth [] = .ok (v, p) := by rw [continueWith]

/--
A comma after an array element sends the machine on to the next element. The frame is kept and the
completed value pushed into it, which is how an array is accumulated.

`hb` says the character after the whitespace at `p` is `','`. The conclusion equates the call with
`value` at the position after the following whitespace, with `v` pushed onto the frame's elements.
The depth is unchanged, no container having been entered or left.
-/
private theorem continueWith_arr_sep {p after : s.Pos} {v : Json} {elems : Array Json}
    {outer : List Frame} (hb : step? (skipWs p).pos = some (',', after)) :
    continueWith cfg v p depth (.arr elems :: outer) =
      value cfg (skipWs after).pos depth (.arr (elems.push v) :: outer) := by
  rw [continueWith]
  simp only []
  split <;> rename_i heq <;> rw [hb] at heq <;> simp at heq
  · subst heq
    rfl
  · obtain ⟨rfl, rfl⟩ := heq
    rename_i hn _
    exact (hn rfl).elim

/--
A closing bracket after an array element completes the array and hands it to the frame outside. It
is where a frame is popped and the depth counter falls.

`hb` says the character after the whitespace at `p` is `']'`. The conclusion equates the call with
`continueWith` on the finished array, at a depth one less and with the outer stack. The element in
hand is pushed before the array is closed, so it is part of what is handed on.
-/
private theorem continueWith_arr_close {p after : s.Pos} {v : Json} {elems : Array Json}
    {outer : List Frame} (hb : step? (skipWs p).pos = some (']', after)) :
    continueWith cfg v p depth (.arr elems :: outer) =
      continueWith cfg (.arr (elems.push v)) after (depth - 1) outer := by
  rw [continueWith]
  simp only []
  split <;> rename_i heq <;> rw [hb] at heq <;> simp at heq
  · subst heq
    rfl
  · obtain ⟨rfl, rfl⟩ := heq
    rename_i _ hn
    exact (hn rfl).elim

/--
A comma after an object member sends the machine on to the next member. The frame's name is paired
with the value just completed and pushed, which is how an object is accumulated.

`hb` says the character after the whitespace at `p` is `','`. The conclusion equates the call with
`member` at the position after the following whitespace, with `(name, v)` pushed onto the frame's
fields and the set of names seen carried across unchanged. The depth is unchanged.
-/
private theorem continueWith_obj_sep {p after : s.Pos} {v : Json}
    {fields : Array (String × Json)} {seen : Std.HashSet String} {name : String}
    {outer : List Frame} (hb : step? (skipWs p).pos = some (',', after)) :
    continueWith cfg v p depth (.obj fields seen name :: outer) =
      member cfg (skipWs after).pos depth (fields.push (name, v)) seen outer := by
  rw [continueWith]
  simp only []
  split <;> rename_i heq <;> rw [hb] at heq <;> simp at heq
  · subst heq
    rfl
  · obtain ⟨rfl, rfl⟩ := heq
    rename_i hn _
    exact (hn rfl).elim

/--
A closing brace after an object member completes the object and hands it to the frame outside. It
is the object's counterpart to closing an array, and where an object frame is popped.

`hb` says the character after the whitespace at `p` is `'}'`. The conclusion equates the call with
`continueWith` on the finished object, at a depth one less and with the outer stack. The name and
the value in hand are paired and pushed before the object is closed. The set of names seen is
discarded, having no place in the finished value.
-/
private theorem continueWith_obj_close {p after : s.Pos} {v : Json}
    {fields : Array (String × Json)} {seen : Std.HashSet String} {name : String}
    {outer : List Frame} (hb : step? (skipWs p).pos = some ('}', after)) :
    continueWith cfg v p depth (.obj fields seen name :: outer) =
      continueWith cfg (.obj (fields.push (name, v))) after (depth - 1) outer := by
  rw [continueWith]
  simp only []
  split <;> rename_i heq <;> rw [hb] at heq <;> simp at heq
  · subst heq
    rfl
  · obtain ⟨rfl, rfl⟩ := heq
    rename_i _ hn
    exact (hn rfl).elim

/--
Having read a member's name and its colon, the machine goes on to read the value. It is the one
place the duplicate-name test is applied, so the lemma has to carry the condition under which that
test does not fire.

`hc` and `hstr` say the name scanned, `hdup` says the duplicate test answered `false`, and `hb`
says a colon follows the whitespace. The conclusion equates the call with `value` at the position
after the colon's whitespace, with an object frame carrying the fields so far, the name added to
the set, and the name itself. `hdup` cannot be dropped: were it true the machine would return an
error rather than descend.
-/
private theorem member_value {p q after : s.Pos} {fields : Array (String × Json)}
    {seen : Std.HashSet String} {r : Scanned String q} (hc : step? p = some ('"', q))
    (hstr : string q "" = .ok r)
    (hdup : (cfg.duplicateKeys == .reject && seen.contains r.value) = false)
    (hb : step? (skipWs r.pos).pos = some (':', after)) :
    member cfg p depth fields seen stack =
      value cfg (skipWs after).pos depth (.obj fields (seen.insert r.value) r.value :: stack) := by
  rw [member]
  split <;> rename_i heq <;> rw [hc] at heq <;> simp at heq
  · subst heq
    simp only [hstr, hdup, Bool.false_eq_true, ite_false]
    split <;> rename_i heq2 <;> rw [hb] at heq2 <;> simp at heq2
    · subst heq2
      rfl
    · obtain ⟨rfl, rfl⟩ := heq2
      rename_i hn
      exact (hn rfl).elim
  · obtain ⟨rfl, -⟩ := heq
    rename_i hn
    exact (hn rfl).elim

/--
The text after an array element is text a value may be followed by. A number's reading depends on
what comes after it, so every element of an array needs `Follows` at its end, and this is where
that comes from.

`h : ElementsRest t vs r` says `t` is the rest of the array: either the closing bracket, or a
separator and more elements. `Spec.Follows t` says `t` is empty or begins with whitespace, a
comma, or a closing bracket or brace. Both cases go through `Spec.follows_of_token`, at `']'` and
at `','` respectively.
-/
private theorem elementsRest_follows {t : List Char} {vs : List Json} {r : List Char}
    (h : ElementsRest t vs r) : Spec.Follows t := by
  cases h with
  | close hend => exact Spec.follows_of_token hend (.inr (.inl rfl))
  | more hsep _ _ => exact Spec.follows_of_token hsep (.inl rfl)

/--
The text after an object member is text a value may be followed by. It is what supplies `Follows`
at the end of a member's value, which the number productions need in order to have one reading.

`h : MembersRest t ms r` says `t` is the rest of the object: either the closing brace, or a
separator and more members. `Spec.Follows t` places its first character among whitespace, a comma
and the two closing characters. Both cases go through `Spec.follows_of_token`, at `'}'` and at
`','`.
-/
private theorem membersRest_follows {t : List Char} {ms : List (String × Json)} {r : List Char}
    (h : MembersRest t ms r) : Spec.Follows t := by
  cases h with
  | close hend => exact Spec.follows_of_token hend (.inr (.inr rfl))
  | more hsep _ _ => exact Spec.follows_of_token hsep (.inl rfl)

/-!
Refusing a repeated name is the one thing the machine does that the grammar does not ask for, so
completeness for the strict reading has to show that the refusal never fires on a value whose
names are distinct. Two halves: what the frame's set holds is among the names the frame will
hold, which is an invariant of the machine, and the object under construction inherits its
distinct names from the value the whole parse returns, which is what `Closes` carries.
-/

/--
Every element of a key-unique array is itself key-unique. The check is a conjunction down the
list, and this is the projection that reaches a single element of it.

`uniqueKeysList l = true` says every element passes, and the conclusion applies that to any
`v ∈ l`. The induction is on `l`; at the empty list there is no member to produce, so that case
carries nothing, which is why the claim is only useful at lists a frame actually holds.
-/
private theorem uniqueKeysList_mem : ∀ {l : List Json}, uniqueKeysList l = true →
    ∀ {v : Json}, v ∈ l → UniqueKeys v := by
  intro l
  induction l with
  | nil => intro _ v hv; exact absurd hv (by simp)
  | cons _ _ ih =>
    intro h v hv
    rw [uniqueKeysList, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hv with rfl | hv
    · exact h.1
    · exact ih h.2 hv

/--
Every value in a key-unique object's fields is itself key-unique. It is the object counterpart of
the array projection, and like the check it is stated of, it looks only at values: whether the
names repeat is `distinctNames`' separate business.

`uniqueKeysFields l = true` says every field's value passes, and the conclusion applies that to
any `m ∈ l`, through `m.2`. The name `m.1` plays no part on either side. The induction is on
`l`.
-/
private theorem uniqueKeysFields_mem : ∀ {l : List (String × Json)}, uniqueKeysFields l = true →
    ∀ {m : String × Json}, m ∈ l → UniqueKeys m.2 := by
  intro l
  induction l with
  | nil => intro _ m hm; exact absurd hm (by simp)
  | cons a _ ih =>
    intro h m hm
    obtain ⟨_, _⟩ := a
    rw [uniqueKeysFields, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.1
    · exact ih h.2 hm

/--
A value the frames still hold is a part of the value the parse returns, so it inherits that
value's key uniqueness. The machine's duplicate test has to be shown never to fire on a text the
grammar derives into a key-unique value, and the value in hand is not the returned one, so the
property has to be carried down the stack.

The induction is on the stack. `Closes stack v t j r` says the frames turn `v` into `j`, and
`UniqueKeys j` is assumed of the finished value. The conclusion `UniqueKeys v` holds because each
frame places `v` inside the container it builds, so `uniqueKeysList_mem` or `uniqueKeysFields_mem`
extracts it again; the empty stack is the case where `v` is `j` itself.
-/
private theorem closes_uniqueKeys : ∀ (stack : List Frame) {v : Json} {t : List Char} {j : Json}
    {r : List Char}, Closes stack v t j r → UniqueKeys j → UniqueKeys v := by
  intro stack
  induction stack with
  | nil =>
    intro v t j r h hj
    simp only [Closes] at h
    obtain ⟨rfl, -⟩ := h
    exact hj
  | cons f outer ih =>
    intro v t j r h hj
    cases f with
    | arr elems =>
      simp only [Closes] at h
      obtain ⟨vs, t', -, h'⟩ := h
      have hu := ih h' hj
      rw [UniqueKeys, uniqueKeys] at hu
      exact uniqueKeysList_mem hu (by simp)
    | obj fields seen name =>
      simp only [Closes] at h
      obtain ⟨ms, t', -, h'⟩ := h
      have hu := ih h' hj
      rw [UniqueKeys, uniqueKeys, Bool.and_eq_true] at hu
      exact uniqueKeysFields_mem hu.2 (m := (name, v)) (by simp)

/--
A name still to be read is not one of the names already read into the same object. This is the
other half of showing the duplicate test never fires: the fields a frame holds and the member
about to be read cannot share a name.

`h` says the whole object, the fields already read followed by the member `m` and those after it,
has distinct names. The conclusion `m.1 ∉ fieldNames fields` isolates the part that matters. It
comes from `distinctNames_iff` and `List.nodup_append`, whose cross condition is exactly that no
name on the left occurs on the right.
-/
private theorem name_not_read {fields : Array (String × Json)} {m : String × Json}
    {ms : List (String × Json)} (h : UniqueKeys (.obj (fields ++ (m :: ms).toArray))) :
    m.1 ∉ fieldNames fields := by
  rw [UniqueKeys, uniqueKeys, Bool.and_eq_true, distinctNames_iff] at h
  have hd := h.1
  rw [show fieldNames (fields ++ (m :: ms).toArray)
        = fieldNames fields ++ (m.1 :: ms.map (·.1)) by simp [fieldNames],
    List.nodup_append] at hd
  intro hm
  exact hd.2.2 m.1 hm m.1 (by simp) rfl

/-- What an object frame's set of names seen may hold: nothing the frame will not. -/
private def SeenOk (names : List String) (seen : Std.HashSet String) : Prop :=
  ∀ nm, seen.contains nm = true → nm ∈ names

private def FrameSeenOk : Frame → Prop
  | .arr _ => True
  | .obj fields seen name => SeenOk (fieldNames fields ++ [name]) seen

private def StackSeenOk (stack : List Frame) : Prop := ∀ f ∈ stack, FrameSeenOk f

/-!
The parser's depth counter is the number of frames it is holding, and a frame is a container the
value it returns nests inside, so the counter never exceeds the depth of that value. A limit on
nesting therefore refuses nothing whose depth is within it.
-/

/--
A parse holding some number of frames is building a value at least that deep. This is the
accounting that lets a configured nesting limit be checked against the counter the machine
carries rather than against a value it has not finished reading.

The induction is on the stack. `Closes stack v t j r` says the frames turn `v` into `j`, and the
conclusion `stack.length + Json.depth v ≤ Json.depth j` counts one for every frame.
`Json.depth_arr_lt` and `Json.depth_obj_lt` supply the strict step at each frame, which is what
pays for the length; the empty stack is where `v` is `j` and the count is zero.
-/
private theorem closes_depth : ∀ (stack : List Frame) {v : Json} {t : List Char} {j : Json}
    {r : List Char}, Closes stack v t j r → stack.length + Json.depth v ≤ Json.depth j := by
  intro stack
  induction stack with
  | nil =>
    intro v t j r h
    simp only [Closes] at h
    obtain ⟨rfl, -⟩ := h
    simp
  | cons f outer ih =>
    intro v t j r h
    cases f with
    | arr elems =>
      simp only [Closes] at h
      obtain ⟨vs, t', -, h'⟩ := h
      have hlt : Json.depth v < Json.depth (.arr (elems.push v ++ vs.toArray)) :=
        Json.depth_arr_lt (by simp)
      have := ih h'
      simp only [List.length_cons]
      omega
    | obj fields seen name =>
      simp only [Closes] at h
      obtain ⟨ms, t', -, h'⟩ := h
      have hlt : Json.depth v < Json.depth (.obj (fields.push (name, v) ++ ms.toArray)) :=
        Json.depth_obj_lt (k := name) (by simp)
      have := ih h'
      simp only [List.length_cons]
      omega

/--
The depth test does not fire while the value being built fits within the configured limit. It is
what turns the depth hypothesis of `parse_complete` into the machine never refusing.

`hlen` says the counter is the number of frames, `hcl` places the value in hand inside the
returned one, `hfit` is the configured bound on that value's depth, and `hv` says the value in
hand has depth at least one, which is what makes the count strict enough to close the arithmetic.
The conclusion covers both cases of the test: with no limit configured it is `false` outright, and
with one, `closes_depth` and `hfit` together bound the counter below it.
-/
private theorem depthExceeded_false {cfg : Config} {depth : Nat} {stack : List Frame}
    {v j : Json} {t r : List Char} (hlen : depth = stack.length) (hcl : Closes stack v t j r)
    (hfit : ∀ limit, cfg.maxDepth = some limit → Json.depth j ≤ limit) (hv : 1 ≤ Json.depth v) :
    depthExceeded cfg depth = false := by
  rw [depthExceeded]
  split
  · next limit hlim =>
    have := closes_depth stack hcl
    have := hfit limit hlim
    simp only [decide_eq_false_iff_not, Nat.not_le]
    omega
  · rfl

/--
The condition on the frames' name sets survives a push. Every descent into a container pushes a
frame, and the invariant has to be re-established there without revisiting the frames below.

`hf` says the new frame satisfies the condition and `hs` says the frames already there do.
`StackSeenOk` is a claim about every member of the list, so the conclusion follows by splitting an
arbitrary membership proof into the head case, which is `hf`, and the tail case, which is `hs`.
-/
private theorem stackSeenOk_cons {f : Frame} {stack : List Frame} (hf : FrameSeenOk f)
    (hs : StackSeenOk stack) : StackSeenOk (f :: stack) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hs g hg

/--
A stack in good order stays in good order when its top frame is removed. Popping a frame is how a
container is closed, and what remains has to still satisfy the invariant.

`hs : StackSeenOk (f :: stack)` is the invariant on the whole stack, and `StackSeenOk stack`
restricts it to the tail. Nothing about `f` is used, so it holds whatever the popped frame was.
-/
private theorem stackSeenOk_tail {f : Frame} {stack : List Frame}
    (hs : StackSeenOk (f :: stack)) : StackSeenOk stack :=
  fun g hg => hs g (List.mem_cons_of_mem _ hg)

/--
The top frame of a stack in good order is itself in good order. It is the projection used wherever
a frame's own set of names has to be reasoned about.

`hs : StackSeenOk (f :: stack)` is the invariant on the whole stack, and `FrameSeenOk f`
instantiates it at the head. For an array frame the condition is `True`, so the projection is only
of interest at an object frame.
-/
private theorem stackSeenOk_head {f : Frame} {stack : List Frame}
    (hs : StackSeenOk (f :: stack)) : FrameSeenOk f := hs f List.mem_cons_self

/--
An empty set of names seen holds nothing it should not. It is where the invariant starts, a fresh
object frame carrying no names at all.

`SeenOk names ∅` says every name the set contains is among `names`. The set contains nothing, so
the claim holds for any `names` whatever, the empty list included; it is not vacuous in use, being
the case a newly opened object frame is in.
-/
private theorem seenOk_empty {names : List String} : SeenOk names (∅ : Std.HashSet String) := by
  intro nm h
  simp at h

/--
Adding a name to the set keeps the invariant, provided the name is added to what the frame will
hold as well. Each member read extends both, and this is the step that keeps them aligned.

`h : SeenOk names seen` is the invariant so far, and the conclusion
`SeenOk (names ++ [name]) (seen.insert name)` extends both sides by the same name. The proof
splits `Std.HashSet.contains_insert`: a name the extended set holds is either the one just added,
which is now at the end of `names`, or one that was already there.
-/
private theorem seenOk_insert {names : List String} {seen : Std.HashSet String} {name : String}
    (h : SeenOk names seen) : SeenOk (names ++ [name]) (seen.insert name) := by
  intro nm hnm
  rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hnm
  rcases hnm with hnm | hnm
  · rw [eq_of_beq hnm]
    simp
  · exact List.mem_append_left _ (h nm hnm)

/-!
The machine, in the direction soundness does not go. What a derivation leaves is what the parser
leaves up to whitespace, since a token in the grammar carries the whitespace after it while the
scanner passes over that only when it next looks, so the conclusions are stated with `Ws` rather
than with equality.
-/

private def ValueComplete (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (stack : List Frame) (l : List Char) (v j : Json) (t r : List Char),
    remaining p = l → Spec.NoWs l → Spec.Value l v t → Spec.Follows t → Closes stack v t j r →
      StackSeenOk stack → (cfg.duplicateKeys = .allow ∨ UniqueKeys j) → depth = stack.length →
        (∀ limit, cfg.maxDepth = some limit → Json.depth j ≤ limit) →
          ∃ rp, value cfg p depth stack = .ok (j, rp) ∧ Spec.Ws (remaining rp) r

private def ContinueComplete (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (v j : Json) (depth : Nat) (stack : List Frame) (t r : List Char),
    Spec.Ws (remaining p) t → Closes stack v t j r → StackSeenOk stack →
      (cfg.duplicateKeys = .allow ∨ UniqueKeys j) → depth = stack.length →
        (∀ limit, cfg.maxDepth = some limit → Json.depth j ≤ limit) →
          ∃ rp, continueWith cfg v p depth stack = .ok (j, rp) ∧ Spec.Ws (remaining rp) r

private def MemberComplete (cfg : Config) (p : s.Pos) : Prop :=
  ∀ (depth : Nat) (fields : Array (String × Json)) (seen : Std.HashSet String)
      (stack : List Frame) (l : List Char) (m : String × Json) (ms : List (String × Json))
      (t₁ t : List Char) (j : Json) (r : List Char),
    remaining p = l → Spec.NoWs l → Spec.Member l m t₁ → MembersRest t₁ ms t →
      Closes stack (.obj (fields ++ (m :: ms).toArray)) t j r →
        SeenOk (fieldNames fields) seen → StackSeenOk stack →
          (cfg.duplicateKeys = .allow ∨ UniqueKeys j) → depth = stack.length + 1 →
            (∀ limit, cfg.maxDepth = some limit → Json.depth j ≤ limit) →
              ∃ rp, member cfg p depth fields seen stack = .ok (j, rp) ∧ Spec.Ws (remaining rp) r

/--
Whatever the grammar derives, the machine reads, at any point in its run and with any stack of
frames. `value`, `continueWith` and `member` call one another, so none can be described alone;
this is the statement provable of all three together, and the entry points below are its
instances.

`hdig` turns the digit limit off, without which a long significand would be refused. `n` bounds
the bytes remaining and the induction runs on `n`, every call being made at a strictly later
position. Each conjunct takes a derivation of what the text holds, a `Closes` saying what the
frames still owe, and the four conditions that keep the machine from refusing: `StackSeenOk`, so
the duplicate test is honest; either duplicates allowed or the returned value key-unique; the
depth counter equal to the number of frames; and the returned value within any configured nesting
limit. Each conclusion produces the position the machine stops at, with `j` returned and
`Spec.Ws (remaining rp) r` rather than an equality, because a token in the grammar carries the
whitespace after it while the scanner passes over that only when it next looks.
-/
private theorem machine_complete {cfg : Config} (hdig : cfg.maxNumberDigits = none) :
    ∀ (n : Nat) (p : s.Pos), p.remainingBytes ≤ n →
      ValueComplete cfg p ∧ ContinueComplete cfg p ∧ MemberComplete cfg p := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro p hp
    refine ⟨?_, ?_, ?_⟩
    · intro depth stack l v j t r hl hnw hv hft hcl hss hok hlen hfit
      cases hv with
      | null =>
        obtain ⟨q, hc, hq⟩ := step_of_remaining hl
        obtain ⟨e, hex, hep⟩ :=
          expect?_complete (p := q) (l := ['u', 'l', 'l']) (u := t) (by simpa using hq)
        have hlt : e.pos.remainingBytes < n := by
          have := step?_lt hc
          have := e.notLonger
          omega
        obtain ⟨rp, hres, hws⟩ := (ih _ hlt e.pos (Nat.le_refl _)).2.1 .null j depth stack t r
          (by rw [hep]; exact Spec.Ws.nil) hcl hss hok hlen hfit
        exact ⟨rp, by rw [value_null hc hex]; exact hres, hws⟩
      | true_ =>
        obtain ⟨q, hc, hq⟩ := step_of_remaining hl
        obtain ⟨e, hex, hep⟩ :=
          expect?_complete (p := q) (l := ['r', 'u', 'e']) (u := t) (by simpa using hq)
        have hlt : e.pos.remainingBytes < n := by
          have := step?_lt hc
          have := e.notLonger
          omega
        obtain ⟨rp, hres, hws⟩ :=
          (ih _ hlt e.pos (Nat.le_refl _)).2.1 (.bool true) j depth stack t r
            (by rw [hep]; exact Spec.Ws.nil) hcl hss hok hlen hfit
        exact ⟨rp, by rw [value_true hc hex]; exact hres, hws⟩
      | false_ =>
        obtain ⟨q, hc, hq⟩ := step_of_remaining hl
        obtain ⟨e, hex, hep⟩ :=
          expect?_complete (p := q) (l := ['a', 'l', 's', 'e']) (u := t) (by simpa using hq)
        have hlt : e.pos.remainingBytes < n := by
          have := step?_lt hc
          have := e.notLonger
          omega
        obtain ⟨rp, hres, hws⟩ :=
          (ih _ hlt e.pos (Nat.le_refl _)).2.1 (.bool false) j depth stack t r
            (by rw [hep]; exact Spec.Ws.nil) hcl hss hok hlen hfit
        exact ⟨rp, by rw [value_false hc hex]; exact hres, hws⟩
      | str hs =>
        obtain ⟨q, res, hc, hstr, hval, hpos⟩ := str_complete hl hs
        have hlt : res.pos.remainingBytes < n := by
          have := step?_lt hc
          have := res.consumed
          omega
        obtain ⟨rp, hres, hws⟩ :=
          (ih _ hlt res.pos (Nat.le_refl _)).2.1 (.str res.value) j depth stack t r
            (by rw [hpos]; exact Spec.Ws.nil) (by rw [hval]; exact hcl) hss hok hlen hfit
        exact ⟨rp, by rw [value_str hc hstr]; exact hres, hws⟩
      | num hn =>
        obtain ⟨c, u, hcu, hcd⟩ := Spec.num_head hn
        obtain ⟨q, hc, -⟩ := step_of_remaining (hl.trans hcu)
        obtain ⟨rn, hnum, hnv, hnp⟩ := number_complete (by rw [hl]; exact hn) hft hdig
        have hlt : rn.pos.remainingBytes < n := by
          have := rn.consumed
          omega
        obtain ⟨rp, hres, hws⟩ :=
          (ih _ hlt rn.pos (Nat.le_refl _)).2.1 (.num rn.value) j depth stack t r
            (by rw [hnp]; exact Spec.Ws.nil) (by rw [hnv]; exact hcl) hss hok hlen hfit
        refine ⟨rp, ?_, hws⟩
        rw [value_num hc ?_ hnum]
        · exact hres
        · rcases hcd with rfl | hd
          · decide
          · simp [hd]
      | arr ha =>
        cases ha with
        | @empty _ s₂ _ hb hend =>
          cases hb with
          | @mk s₁ _ hlead htrail =>
            cases hend with
            | @mk u _ hlead₂ htrail₂ =>
              obtain ⟨q, hc, hq⟩ := step_of_remaining (hl.trans (hlead.source_eq_of_noWs hnw))
              have hstep : remaining (skipWs q).pos = ']' :: u :=
                skipWs_complete (by rw [hq]; exact htrail.trans hlead₂)
                  (Spec.noWs_cons (by decide))
              obtain ⟨after, hb₂, hafter⟩ := step_of_remaining hstep
              have hlt : after.remainingBytes < n := by
                have := step?_lt hc
                have := (skipWs q).notLonger
                have := step?_lt hb₂
                omega
              obtain ⟨rp, hres, hws⟩ :=
                (ih _ hlt after (Nat.le_refl _)).2.1 (.arr #[]) j depth stack t r
                  (by rw [hafter]; exact htrail₂) hcl hss hok hlen hfit
              refine ⟨rp, ?_, hws⟩
              rw [value_arr_empty hc
                (depthExceeded_false hlen hcl hfit (by simp [Json.depth])) hb₂]
              exact hres
        | @items _ s₂ s₃ vs _ hb hels hend =>
          cases hb with
          | @mk s₁ _ hlead htrail =>
            obtain ⟨q, hc, hq⟩ := step_of_remaining (hl.trans (hlead.source_eq_of_noWs hnw))
            have hshift : Spec.Ws s₂ (remaining (skipWs q).pos) :=
              Spec.Ws.to_noWs htrail (by rw [← hq]; exact ws_skipWs q) (noWs_skipWs q)
            obtain ⟨v₁, vs', t₁, rfl, hv₁, hrest⟩ :=
              elementsEnd_uncons (Spec.elements_ws hshift hels) hend
            have hnb : ∀ after, step? (skipWs q).pos ≠ some (']', after) := by
              intro after hb₂
              exact Spec.not_value_bracket (remaining_step hb₂ ▸ hv₁)
            have hlt : (skipWs q).pos.remainingBytes < n := by
              have := step?_lt hc
              have := (skipWs q).notLonger
              omega
            obtain ⟨rp, hres, hws⟩ :=
              (ih _ hlt (skipWs q).pos (Nat.le_refl _)).1 (depth + 1) (.arr #[] :: stack)
                (remaining (skipWs q).pos) v₁ j t₁ r rfl (noWs_skipWs q) hv₁
                (elementsRest_follows hrest) (by simp only [Closes]; exact ⟨vs', t, hrest,
                  by simpa using hcl⟩) (stackSeenOk_cons trivial hss) hok (by simp [hlen]) hfit
            refine ⟨rp, ?_, hws⟩
            rw [value_arr_items hc (depthExceeded_false hlen hcl hfit (by simp [Json.depth])) hnb]
            exact hres
      | obj ho =>
        cases ho with
        | @empty _ s₂ _ hb hend =>
          cases hb with
          | @mk s₁ _ hlead htrail =>
            cases hend with
            | @mk u _ hlead₂ htrail₂ =>
              obtain ⟨q, hc, hq⟩ := step_of_remaining (hl.trans (hlead.source_eq_of_noWs hnw))
              have hstep : remaining (skipWs q).pos = '}' :: u :=
                skipWs_complete (by rw [hq]; exact htrail.trans hlead₂)
                  (Spec.noWs_cons (by decide))
              obtain ⟨after, hb₂, hafter⟩ := step_of_remaining hstep
              have hlt : after.remainingBytes < n := by
                have := step?_lt hc
                have := (skipWs q).notLonger
                have := step?_lt hb₂
                omega
              obtain ⟨rp, hres, hws⟩ :=
                (ih _ hlt after (Nat.le_refl _)).2.1 (.obj #[]) j depth stack t r
                  (by rw [hafter]; exact htrail₂) hcl hss hok hlen hfit
              refine ⟨rp, ?_, hws⟩
              rw [value_obj_empty hc
                (depthExceeded_false hlen hcl hfit (by simp [Json.depth])) hb₂]
              exact hres
        | @members _ s₂ s₃ ms _ hb hms hend =>
          cases hb with
          | @mk s₁ _ hlead htrail =>
            obtain ⟨q, hc, hq⟩ := step_of_remaining (hl.trans (hlead.source_eq_of_noWs hnw))
            have hshift : Spec.Ws s₂ (remaining (skipWs q).pos) :=
              Spec.Ws.to_noWs htrail (by rw [← hq]; exact ws_skipWs q) (noWs_skipWs q)
            obtain ⟨m₁, ms', t₁, rfl, hm₁, hrest⟩ :=
              membersEnd_uncons (Spec.members_ws hshift hms) hend
            have hnb : ∀ after, step? (skipWs q).pos ≠ some ('}', after) := by
              intro after hb₂
              exact Spec.not_members_brace (remaining_step hb₂ ▸ Spec.Members.one hm₁)
            have hlt : (skipWs q).pos.remainingBytes < n := by
              have := step?_lt hc
              have := (skipWs q).notLonger
              omega
            obtain ⟨rp, hres, hws⟩ :=
              (ih _ hlt (skipWs q).pos (Nat.le_refl _)).2.2 (depth + 1) #[] ∅ stack
                (remaining (skipWs q).pos) m₁ ms' t₁ t j r rfl (noWs_skipWs q) hm₁ hrest
                (by simpa using hcl) seenOk_empty hss hok (by simp [hlen]) hfit
            refine ⟨rp, ?_, hws⟩
            rw [value_obj_members hc
              (depthExceeded_false hlen hcl hfit (by simp [Json.depth])) hnb]
            exact hres
    · intro v j depth stack t r hws hcl hss hok hlen hfit
      cases stack with
      | nil =>
        simp only [Closes] at hcl
        obtain ⟨rfl, rfl⟩ := hcl
        exact ⟨p, continueWith_nil, hws⟩
      | cons f outer =>
        cases f with
        | arr elems =>
          simp only [Closes] at hcl
          obtain ⟨vs, t', hrest, hcl₂⟩ := hcl
          cases hrest with
          | @close _ _ hend =>
            cases hend with
            | @mk u _ hlead htrail =>
              have hstep : remaining (skipWs p).pos = ']' :: u :=
                skipWs_complete (hws.trans hlead) (Spec.noWs_cons (by decide))
              obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
              have hlt : after.remainingBytes < n := by
                have := (skipWs p).notLonger
                have := step?_lt hb
                omega
              obtain ⟨rp, hres, hwsr⟩ :=
                (ih _ hlt after (Nat.le_refl _)).2.1 (.arr (elems.push v)) j (depth - 1) outer t' r
                  (by rw [hafter]; exact htrail) (by simpa using hcl₂) (stackSeenOk_tail hss) hok
                  (by simp only [List.length_cons] at hlen; omega) hfit
              exact ⟨rp, by rw [continueWith_arr_close hb]; exact hres, hwsr⟩
          | @more _ t₁ t₂ v₂ vs' _ hsep hv hrest₂ =>
            cases hsep with
            | @mk u _ hlead htrail =>
              have hstep : remaining (skipWs p).pos = ',' :: u :=
                skipWs_complete (hws.trans hlead) (Spec.noWs_cons (by decide))
              obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
              have hshift : Spec.Ws t₁ (remaining (skipWs after).pos) :=
                Spec.Ws.to_noWs htrail (by rw [← hafter]; exact ws_skipWs after)
                  (noWs_skipWs after)
              have hlt : (skipWs after).pos.remainingBytes < n := by
                have := (skipWs p).notLonger
                have := step?_lt hb
                have := (skipWs after).notLonger
                omega
              obtain ⟨rp, hres, hwsr⟩ :=
                (ih _ hlt (skipWs after).pos (Nat.le_refl _)).1 depth
                  (.arr (elems.push v) :: outer) (remaining (skipWs after).pos) v₂ j t₂ r rfl
                  (noWs_skipWs after) (Spec.value_ws hshift hv) (elementsRest_follows hrest₂)
                  (by simp only [Closes]; exact ⟨vs', t', hrest₂, by simpa using hcl₂⟩)
                  (stackSeenOk_cons trivial (stackSeenOk_tail hss)) hok
                  (by simp only [List.length_cons] at hlen ⊢; omega) hfit
              exact ⟨rp, by rw [continueWith_arr_sep hb]; exact hres, hwsr⟩
        | obj fields seen name =>
          simp only [Closes] at hcl
          obtain ⟨ms, t', hrest, hcl₂⟩ := hcl
          cases hrest with
          | @close _ _ hend =>
            cases hend with
            | @mk u _ hlead htrail =>
              have hstep : remaining (skipWs p).pos = '}' :: u :=
                skipWs_complete (hws.trans hlead) (Spec.noWs_cons (by decide))
              obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
              have hlt : after.remainingBytes < n := by
                have := (skipWs p).notLonger
                have := step?_lt hb
                omega
              obtain ⟨rp, hres, hwsr⟩ :=
                (ih _ hlt after (Nat.le_refl _)).2.1 (.obj (fields.push (name, v))) j (depth - 1)
                  outer t' r (by rw [hafter]; exact htrail) (by simpa using hcl₂)
                  (stackSeenOk_tail hss) hok
                  (by simp only [List.length_cons] at hlen; omega) hfit
              exact ⟨rp, by rw [continueWith_obj_close hb]; exact hres, hwsr⟩
          | @more _ t₁ t₂ m₂ ms' _ hsep hm hrest₂ =>
            cases hsep with
            | @mk u _ hlead htrail =>
              have hstep : remaining (skipWs p).pos = ',' :: u :=
                skipWs_complete (hws.trans hlead) (Spec.noWs_cons (by decide))
              obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
              have hshift : Spec.Ws t₁ (remaining (skipWs after).pos) :=
                Spec.Ws.to_noWs htrail (by rw [← hafter]; exact ws_skipWs after)
                  (noWs_skipWs after)
              have hlt : (skipWs after).pos.remainingBytes < n := by
                have := (skipWs p).notLonger
                have := step?_lt hb
                have := (skipWs after).notLonger
                omega
              obtain ⟨rp, hres, hwsr⟩ :=
                (ih _ hlt (skipWs after).pos (Nat.le_refl _)).2.2 depth (fields.push (name, v))
                  seen outer (remaining (skipWs after).pos) m₂ ms' t₂ t' j r rfl
                  (noWs_skipWs after) (Spec.member_ws hshift hm) hrest₂ (by simpa using hcl₂)
                  (by
                    have hf := stackSeenOk_head hss
                    simp only [FrameSeenOk] at hf
                    simpa using hf)
                  (stackSeenOk_tail hss) hok (by simp only [List.length_cons] at hlen; omega) hfit
              exact ⟨rp, by rw [continueWith_obj_sep hb]; exact hres, hwsr⟩
    · intro depth fields seen stack l m ms t₁ t j r hl hnw hm hrest hcl hso hss hok hlen hfit
      cases hm with
      | @mk _ s₂ s₃ k v _ hstr hsep hv =>
        obtain ⟨q, res, hc, hs, hval, hpos⟩ := str_complete hl hstr
        cases hsep with
        | @mk u _ hlead htrail =>
          have hstep : remaining (skipWs res.pos).pos = ':' :: u :=
            skipWs_complete (by rw [hpos]; exact hlead) (Spec.noWs_cons (by decide))
          obtain ⟨after, hb, hafter⟩ := step_of_remaining hstep
          have hshift : Spec.Ws s₃ (remaining (skipWs after).pos) :=
            Spec.Ws.to_noWs htrail (by rw [← hafter]; exact ws_skipWs after) (noWs_skipWs after)
          have hlt : (skipWs after).pos.remainingBytes < n := by
            have := step?_lt hc
            have := res.consumed
            have := (skipWs res.pos).notLonger
            have := step?_lt hb
            have := (skipWs after).notLonger
            omega
          obtain ⟨rp, hres, hwsr⟩ :=
            (ih _ hlt (skipWs after).pos (Nat.le_refl _)).1 depth
              (.obj fields (seen.insert res.value) res.value :: stack)
              (remaining (skipWs after).pos) v j t₁ r rfl (noWs_skipWs after)
              (Spec.value_ws hshift hv) (membersRest_follows hrest)
              (by simp only [Closes]; exact ⟨ms, t, hrest, by rw [hval]; simpa using hcl⟩)
              (stackSeenOk_cons
                (show SeenOk (fieldNames fields ++ [res.value]) (seen.insert res.value) from
                  seenOk_insert hso) hss) hok (by simp only [List.length_cons]; omega) hfit
          have hdup : (cfg.duplicateKeys == .reject && seen.contains res.value) = false := by
            rcases hok with hallow | hu
            · simp [hallow]
            · have hnot : k ∉ fieldNames fields := name_not_read (closes_uniqueKeys stack hcl hu)
              have hs' : seen.contains res.value = false := by
                cases hc' : seen.contains res.value with
                | false => rfl
                | true =>
                  rw [hval] at hc'
                  exact absurd (hso k hc') hnot
              simp [hs']
          refine ⟨rp, ?_, hwsr⟩
          rw [member_value hc hs hdup hb]
          exact hres

/-! ## Text -/

/--
No derivable text begins with a byte order mark, so the parser's leave to ignore one is never
exercised on text the grammar accepts, and the reading does not depend on `ignoreBOM`. Without
this, completeness would have to carry that setting as a hypothesis.

`h : Spec.Text l j` says `l` derives `j`, and `hl` names its first character `c`. The conclusion
`c.toNat ≠ 0xFEFF` denies that character being the mark. Were it the mark it would be neither
whitespace nor a digit, so the leading `Ws` run would consume nothing and `Spec.not_value_cons`
would deny the value; the eight character inequalities that lemma needs all follow from the code
point being `0xFEFF`.
-/
private theorem head_ne_bom {l : List Char} {j : Json} (h : Spec.Text l j) {c : Char}
    {u : List Char} (hl : l = c :: u) : c.toNat ≠ 0xFEFF := by
  intro hbom
  obtain ⟨s₁, s₂, hws, hv, -⟩ := h
  have hne : ∀ d : Char, d.toNat ≠ 0xFEFF → c ≠ d := fun d hd hcd => hd (hcd ▸ hbom)
  have hnw : Spec.isWs c = false := by
    cases hw : Spec.isWs c with
    | false => rfl
    | true =>
      rcases Spec.eq_of_isWs hw with rfl | rfl | rfl | rfl <;> exact absurd hbom (by decide)
  have hd : Spec.isDigit c = false := by
    simp only [Spec.isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not, Char.le_def,
      UInt32.le_iff_toNat_le, Nat.not_le]
    have h9 : ('9' : Char).val.toNat = 57 := rfl
    have hcv : c.val.toNat = 65279 := hbom
    omega
  rw [hl] at hws
  rw [Spec.ws_eq_of_not_isWs hnw hws] at hv
  exact Spec.not_value_cons hnw (hne 'f' (by decide)) (hne 'n' (by decide)) (hne 't' (by decide))
    (hne '"' (by decide)) (hne '[' (by decide)) (hne '{' (by decide)) (hne '-' (by decide)) hd hv

/--
Whatever the grammar derives from the text at `start`, the machine reads, and returns as the value
the grammar gives it. Refusing a repeated name is a restriction of the grammar rather than a
defect, so the strict reading is covered too, on the values whose names are distinct.

`hdig` turns the digit limit off, `hkeys` asks either that repeated names be allowed or that `j`
have none, and `hdepth` asks that `j` fit within any configured nesting limit; each of the three
answers to a setting that refuses legal text by design, and the last holds with nothing to prove
exactly when no limit is set. `h` is the `Text` derivation. The conclusion says both that the
parse succeeds and that it returns `j`. `machine_complete` is applied with an empty stack, where
`Closes` is trivial and `StackSeenOk` has nothing to check, and `skipWs_complete` then closes the
gap between where the machine stopped and the empty remainder `Text` demands.
-/
theorem parseFrom_complete {cfg : Config} (hdig : cfg.maxNumberDigits = none) {start : s.Pos}
    {j : Json} (hkeys : cfg.duplicateKeys = .allow ∨ UniqueKeys j)
    (hdepth : ∀ limit, cfg.maxDepth = some limit → Json.depth j ≤ limit)
    (h : Spec.Text (remaining start) j) : parseFrom cfg start = .ok j := by
  obtain ⟨s₁, s₂, hws, hv, hend⟩ := h
  have hshift : Spec.Ws s₁ (remaining (skipWs start).pos) :=
    Spec.Ws.to_noWs hws (ws_skipWs start) (noWs_skipWs start)
  obtain ⟨rp, hres, hwsr⟩ :=
    (machine_complete hdig (skipWs start).pos.remainingBytes (skipWs start).pos
        (Nat.le_refl _)).1 0 [] (remaining (skipWs start).pos) j j s₂ s₂ rfl (noWs_skipWs start)
      (Spec.value_ws hshift hv) (Spec.follows_of_ws hend) (by simp [Closes])
      (fun f hf => absurd hf (by simp)) hkeys rfl hdepth
  have hnil : remaining (skipWs rp).pos = [] :=
    skipWs_complete (hwsr.trans hend) (fun c t hct => absurd hct (by simp))
  have hstep : step? (skipWs rp).pos = none := by
    cases hs : step? (skipWs rp).pos with
    | none => rfl
    | some cq =>
      obtain ⟨c, q⟩ := cq
      rw [remaining_step hs] at hnil
      exact absurd hnil (by simp)
  simp only [parseFrom, hres, hstep]

/--
The parser never skips a byte order mark in text the grammar derives, so the entry point is the
same function as the one that starts at the beginning. This is what keeps `ignoreBOM` out of the
completeness statement, where it would otherwise have to appear as a hypothesis.

`h : Spec.TextOf s j` is the derivation. The conclusion `parse s cfg = parseFrom cfg s.startPos`
says the mark test does not fire, whatever `cfg.ignoreBOM` is set to. `head_ne_bom` is what makes
the test's condition false; an empty string does not reach the test at all.
-/
private theorem parse_eq_parseFrom {cfg : Config} {j : Json} (h : Spec.TextOf s j) :
    parse s cfg = parseFrom cfg s.startPos := by
  have h' : Spec.Text (remaining s.startPos) j := by rw [remaining_startPos]; exact h
  cases hc : step? s.startPos with
  | none => simp only [parse, hc]
  | some cq =>
    obtain ⟨c, q⟩ := cq
    have hbom := head_ne_bom h' (remaining_step hc)
    simp only [parse, hc, ite_eq_right (by simp [hbom] : ¬(cfg.ignoreBOM && c.toNat == 0xFEFF) = true)]

/--
No false rejects: text the grammar derives is read, and read as the value the grammar gives it.
This is the half of correctness a caller feels, that a document which is JSON is not refused, and
the hypotheses are exactly the settings that refuse legal text by design.

`hdig` turns the digit limit off, `hkeys` asks that repeated names be either allowed or absent,
and `hdepth` asks that `j` sit within any configured nesting limit, which holds with nothing to
prove when no limit is set. `h : Spec.TextOf s j` is the derivation, and the conclusion says the
parse succeeds and returns `j` itself rather than something equal to it in a weaker sense. It is
`parse_eq_parseFrom` followed by `parseFrom_complete` at the string's start.
-/
theorem parse_complete {s : String} {cfg : Config} {j : Json}
    (hdig : cfg.maxNumberDigits = none) (hkeys : cfg.duplicateKeys = .allow ∨ UniqueKeys j)
    (hdepth : ∀ limit, cfg.maxDepth = some limit → Json.depth j ≤ limit)
    (h : Spec.TextOf s j) : parse s cfg = .ok j := by
  rw [parse_eq_parseFrom h]
  exact parseFrom_complete hdig hkeys hdepth (by rw [remaining_startPos]; exact h)

/--
On text the grammar derives, what the parser returns is settled before it is run. That is what
lets the completeness proof ignore the value entirely: all that remains to establish is that the
parse does not fail.

`ht` says `s` derives `j` and `h` says the parse returned `j'`. The conclusion `j' = j` follows
from soundness, `text_parseFrom` giving a derivation for `j'`, together with `Spec.text_unique`,
which says one text derives one value. `parse_eq_parseFrom` is what removes the byte order mark
from the picture, so no hypothesis on `ignoreBOM` is needed here.
-/
theorem eq_of_parse_of_textOf {cfg : Config} {j j' : Json} (ht : Spec.TextOf s j)
    (h : parse s cfg = .ok j') : j' = j := by
  rw [parse_eq_parseFrom ht] at h
  have hs := text_parseFrom h
  rw [remaining_startPos] at hs
  exact Spec.text_unique hs ht

/--
The other half of the strict reading: text that derives a value with a repeated name is refused
rather than read as something else. Together with `parse_complete` that settles what the strict
reading does with every text the grammar derives.

`hkeys` fixes the configuration to `.reject`, `ht` says `s` derives `j`, and `hu` says `j` has a
repeated name somewhere within it. The conclusion produces an error without saying which, the
message being no part of the claim. It is a contradiction: a success would return `j` by
`eq_of_parse_of_textOf` and would be key-unique by `uniqueKeys_parse`, which `hu` denies.
-/
theorem parse_error_of_not_uniqueKeys {cfg : Config} {j : Json}
    (hkeys : cfg.duplicateKeys = .reject) (ht : Spec.TextOf s j) (hu : ¬ UniqueKeys j) :
    ∃ e, parse s cfg = .error e := by
  cases h : parse s cfg with
  | error e => exact ⟨e, rfl⟩
  | ok j' => exact absurd (eq_of_parse_of_textOf ht h ▸ uniqueKeys_parse hkeys h) hu

/--
Bytes that decode to text the grammar derives are read, and read as the value the grammar gives
it. It is the string case with the decoding step in front, which is where RFC 8259 section 8.1's
requirement of UTF-8 is enforced.

`hdig`, `hkeys` and `hdepth` are the same three settings as for a string: the digit limit off,
repeated names allowed or absent, and the value within any configured nesting limit. `hb` says the
bytes decode to `text` and `h` says that text derives `j`. The conclusion says the parse succeeds
and returns `j`. Bytes that do not decode fall outside the hypothesis, `parseBytes` refusing them
before any parsing is attempted.
-/
theorem parseBytes_complete {b : ByteArray} {cfg : Config} {text : String} {j : Json}
    (hdig : cfg.maxNumberDigits = none)
    (hkeys : cfg.duplicateKeys = .allow ∨ UniqueKeys j)
    (hdepth : ∀ limit, cfg.maxDepth = some limit → Json.depth j ≤ limit)
    (hb : String.fromUTF8? b = some text) (h : Spec.TextOf text j) :
    parseBytes b cfg = .ok j := by
  simp only [parseBytes, hb]
  exact parse_complete hdig hkeys hdepth h

end Json.Parser
