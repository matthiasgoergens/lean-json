/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec

public section

namespace Json.Spec

/-!
How much of the text each production consumes.

Every production leaves less text than it was given, and a value leaves strictly less. That is
what lets a proof about the grammar run by induction on the length of the text: the six relations
of the value family are one mutual definition, which the `induction` tactic will not take apart,
but each of them shortens what it is given, so an induction on the length reaches all six.
-/

/--
Whitespace never lengthens what is left to read. It is the one production that may consume nothing
at all, so it is the only one whose bound cannot be made strict, and every other bound in this
module has to account for that when whitespace appears beside it.

`h : Ws s r` says whitespace consumed some prefix of `s` and left `r`. `r.length ≤ s.length` is
non-strict because `Ws.nil` consumes nothing and leaves `r` as `s` itself. The induction is on the
derivation, each `cons` removing exactly one character.
-/
theorem Ws.length_le {s r : List Char} (h : Ws s r) : r.length ≤ s.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => exact Nat.le_succ_of_le ih

/--
A structural character with its surrounding whitespace consumes at least that character. This is
where arrays and objects get their strict bounds: the brackets alone shorten the text, so even an
empty container leaves strictly less than it was given.

`h : Token t s r` says whitespace, then `t`, then whitespace was consumed from `s`, leaving `r`.
`r.length < s.length` is strict because the middle `t` is consumed unconditionally, whatever the
two whitespace runs do; `Ws.length_le` bounds those, and neither can make up the character `t`
takes.
-/
theorem token_length {t : Char} {s r : List Char} (h : Token t s r) :
    r.length < s.length := by
  cases h with
  | mk h₁ h₂ =>
    have l₁ := h₁.length_le
    have l₂ := h₂.length_le
    simp only [List.length_cons] at l₁
    omega

/--
A run of digits consumes at least one character. The ABNF writes `1*DIGIT`, requiring one, and
this is the fact that carries strictness into the number productions, which are otherwise a chain
of optional parts.

`h : Digits s v n r` says the front of `s` is a run of digits denoting `v`, `n` of them, leaving
`r`. `r.length < s.length` is strict because the base case `Digits.last` already consumes a
character; there is no empty derivation. Neither `v` nor `n` appears in the bound.
-/
theorem digits_length {s : List Char} {v n : Nat} {r : List Char} (h : Digits s v n r) :
    r.length < s.length := by
  induction h with
  | last => simp
  | cons _ _ ih => simp only [List.length_cons]; omega

/--
The integer part of a number consumes at least one character. It is the one part of a number that
is not optional, so it is where a number's strict bound has to come from.

`h : Int' s v r` says the front of `s` is an `int` denoting `v`. Both constructors consume:
`Int'.zero` takes the single character `'0'`, and `Int'.digits` takes a leading non-zero digit and
whatever follows, bounded by `digits_length`. So `r.length < s.length` in either case.
-/
theorem int_length {s : List Char} {v : Nat} {r : List Char} (h : Int' s v r) :
    r.length < s.length := by
  cases h with
  | zero => simp
  | digits _ hd => exact digits_length hd

/--
A fraction never lengthens what is left. It is optional, so its bound cannot be strict, and any
claim about a number as a whole has to find its strictness elsewhere.

`h : Frac s f n r` says the front of `s` is an optional `frac` denoting `f` with `n` digits.
`Frac.absent` consumes nothing and leaves `r` as `s`, which is why the bound is `≤`;
`Frac.present` consumes a `'.'` and at least one digit, by `digits_length`, and so takes strictly
more.
-/
theorem frac_length {s : List Char} {f n : Nat} {r : List Char} (h : Frac s f n r) :
    r.length ≤ s.length := by
  cases h with
  | absent => exact Nat.le_refl _
  | present hd => have := digits_length hd; simp only [List.length_cons]; omega

/--
An exponent never lengthens what is left. It too is optional, and it has three ways of being
present, bare or with either sign, each of which has to be bounded on its own.

`h : Exp s e r` says the front of `s` is an optional `exp` denoting `e`. `Exp.absent` consumes
nothing, which is where the non-strict bound comes from; `bare`, `plus` and `minus` each consume
the `e` or `E`, the sign where there is one, and at least one digit by `digits_length`. `e` may be
negative, but nothing in the bound depends on its value.
-/
theorem exp_length {s : List Char} {e : Int} {r : List Char} (h : Exp s e r) :
    r.length ≤ s.length := by
  cases h with
  | absent => exact Nat.le_refl _
  | bare _ hd => have := digits_length hd; simp only [List.length_cons]; omega
  | plus _ hd => have := digits_length hd; simp only [List.length_cons]; omega
  | minus _ hd => have := digits_length hd; simp only [List.length_cons]; omega

/--
A leading minus never lengthens what is left. It is the last of a number's optional parts, and it
is bounded here so that `num_length` can add all four bounds together.

`h : Sign s b r` says the front of `s` is an optional `minus`, `b` recording whether one was
found. `Sign.absent` consumes nothing, hence the `≤`; `Sign.minus` consumes the single character
`'-'`.
-/
theorem sign_length {s : List Char} {b : Bool} {r : List Char} (h : Sign s b r) :
    r.length ≤ s.length := by
  cases h with
  | absent => exact Nat.le_refl _
  | minus => simp

/--
A number consumes at least one character. Three of its four parts are optional, so this rests
entirely on the integer part being required, and it is what lets a number stand as an alternative
of `Value`, whose bound must be strict.

`h : Num s n r` says the front of `s` is a `number` denoting `n`. The bound is the sum of the four
parts in order: `sign_length`, `frac_length` and `exp_length` give `≤`, and `int_length` gives
the one strict step, which is what makes the total strict.
-/
theorem num_length {s : List Char} {n : Number} {r : List Char} (h : Num s n r) :
    r.length < s.length := by
  cases h with
  | mk hs hi hf he =>
    have l₁ := sign_length hs
    have l₂ := int_length hi
    have l₃ := frac_length hf
    have l₄ := exp_length he
    omega

/--
Four hexadecimal digits consume exactly four characters. It is an equation rather than an
inequality because the surrogate-pair rule has to know precisely where the first `\uXXXX` ends in
order to look for a second one there, which a bound alone would not settle.

`h : Hex4 s v r` says the first four characters of `s` are hexadecimal digits denoting `v`, and
`r.length + 4 = s.length` fixes the count exactly. `Hex4` has a single constructor, which matches
four characters explicitly, so nothing is left to case analysis.
-/
theorem hex4_length {s : List Char} {v : Nat} {r : List Char} (h : Hex4 s v r) :
    r.length + 4 = s.length := by
  cases h with
  | mk => simp

/--
One character of a string literal consumes at least one character of the text. A single character
may be spelled in one, two, six or twelve characters, so every constructor has to be bounded and
not merely the literal one.

`h : Ch s c r` says the front of `s` spells the character `c`. `r.length < s.length` is strict in
every case: an unescaped character costs one, the short escapes two, `codePoint` six by
`hex4_length`, and `surrogatePair` twelve by two applications of it. No spelling of a character is
free.
-/
theorem ch_length {s : List Char} {c : Char} {r : List Char} (h : Ch s c r) :
    r.length < s.length := by
  cases h with
  | codePoint hx _ => have := hex4_length hx; simp only [List.length_cons]; omega
  | surrogatePair hx₁ hx₂ _ _ _ _ _ =>
    have := hex4_length hx₁
    have := hex4_length hx₂
    simp only [List.length_cons] at *
    omega
  | _ => simp only [List.length_cons]; omega

/--
A run of string characters never lengthens what is left. It may be empty, the empty string being a
legal literal, which is why the strictness of `Str` cannot come from here.

`h : Chars s cs r` says the front of `s` spells the characters `cs`, leaving `r`. `Chars.nil`
consumes nothing, giving the `≤`; each `cons` consumes at least one character by `ch_length`, so
a non-empty run does shorten the text, though that is not what is claimed.
-/
theorem chars_length {s : List Char} {cs r : List Char} (h : Chars s cs r) :
    r.length ≤ s.length := by
  induction h with
  | nil => exact Nat.le_refl _
  | cons hch _ ih => have := ch_length hch; omega

/--
A string literal consumes at least one character. Its body may be empty, so the bound comes from
the quotation marks rather than the contents; object member names are string literals, so the
member bound depends on this one being strict.

`h : Str s v r` says the front of `s` is a string literal denoting `v`. The single constructor
consumes the opening `'"'`, then a `Chars` run whose bound is only `≤`, then the closing `'"'`.
The two quotation marks are what make the total strict.
-/
theorem str_length {s : List Char} {v : String} {r : List Char} (h : Str s v r) :
    r.length < s.length := by
  cases h with
  | mk hcs =>
    have := chars_length hcs
    simp only [List.length_cons] at *
    omega

/--
Each of the six mutually recursive productions bounds what it leaves against what it was given.
They are one mutual definition, which the `induction` tactic will not take apart, so no one of
them can be bounded alone; this proves all six together, and every other bound in this file is an
instance of it.

`n` bounds the text's length, by `hs : s.length ≤ n`, and the induction runs on `n`, which is
the device the mutual definition forces. `Arr`, `Object` and `Value` get `<`, their brackets or
their leading characters being consumed unconditionally, through `token_length` and the leaf
bounds above. `Elements`, `Member` and `Members` get only `≤`; each of them in fact consumes,
every derivation requiring at least one value, but that is not proved here and nothing downstream
needs it. The bound on `n` cannot empty the claim, since `n := s.length` satisfies `hs` for every
`s`, which is how the six theorems below apply it.
-/
private theorem family_length : ∀ (n : Nat) (s : List Char), s.length ≤ n →
    (∀ {e r}, Arr s e r → r.length < s.length) ∧
    (∀ {f r}, Object s f r → r.length < s.length) ∧
    (∀ {j r}, Value s j r → r.length < s.length) ∧
    (∀ {vs r}, Elements s vs r → r.length ≤ s.length) ∧
    (∀ {m r}, Member s m r → r.length ≤ s.length) ∧
    (∀ {ms r}, Members s ms r → r.length ≤ s.length) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro s hs
    have harr : ∀ {e r}, Arr s e r → r.length < s.length := by
      intro e r h
      cases h with
      | empty hb he => have := token_length hb; have := token_length he; omega
      | items hb hel he =>
        have l₁ := token_length hb
        have l₂ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.1 hel
        have l₃ := token_length he
        omega
    have hobj : ∀ {f r}, Object s f r → r.length < s.length := by
      intro f r h
      cases h with
      | empty hb he => have := token_length hb; have := token_length he; omega
      | members hb hms he =>
        have l₁ := token_length hb
        have l₂ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.2.2 hms
        have l₃ := token_length he
        omega
    have hval : ∀ {j r}, Value s j r → r.length < s.length := by
      intro j r h
      cases h with
      | false_ => simp only [List.length_cons]; omega
      | null => simp only [List.length_cons]; omega
      | true_ => simp only [List.length_cons]; omega
      | num hn => exact num_length hn
      | str hst => exact str_length hst
      | arr ha => exact harr ha
      | obj ho => exact hobj ho
    have hels : ∀ {vs r}, Elements s vs r → r.length ≤ s.length := by
      intro vs r h
      cases h with
      | one hv => exact Nat.le_of_lt (hval hv)
      | more hv hsep hel =>
        have l₁ := hval hv
        have l₂ := token_length hsep
        have l₃ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.1 hel
        omega
    have hmem : ∀ {m r}, Member s m r → r.length ≤ s.length := by
      intro m r h
      cases h with
      | mk hst hsep hv =>
        have l₁ := str_length hst
        have l₂ := token_length hsep
        have l₃ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.1 hv
        omega
    have hmems : ∀ {ms r}, Members s ms r → r.length ≤ s.length := by
      intro ms r h
      cases h with
      | one hm => exact hmem hm
      | more hm hsep hms =>
        have l₁ := hmem hm
        have l₂ := token_length hsep
        have l₃ := (ih _ (by omega) _ (Nat.le_refl _)).2.2.2.2.2 hms
        omega
    exact ⟨harr, hobj, hval, hels, hmem, hmems⟩

/--
An array consumes at least one character of the text. Its brackets alone see to that, so even `[]`
leaves strictly less than it was given, which is what a recursion over an array's contents needs
in order to terminate.

`h : Arr s e r` says the front of `s` is an `array` production yielding the elements `e`. The
elements play no part in the bound: an empty array is bounded by its two brackets, through
`token_length`. It is `family_length` taken at `n := s.length`.
-/
theorem arr_length {s : List Char} {e : Array Json} {r : List Char} (h : Arr s e r) :
    r.length < s.length := (family_length s.length s (Nat.le_refl _)).1 h

/--
An object consumes at least one character of the text. As with an array, the braces guarantee it,
so `{}` is shorter than the text it came from and no object can be entered without progress being
made.

`h : Object s f r` says the front of `s` is an `object` production yielding the fields `f`. The
fields play no part in the bound, an empty object being bounded by its braces alone. It is
`family_length` taken at `n := s.length`.
-/
theorem object_length {s : List Char} {f : Array (String × Json)} {r : List Char}
    (h : Object s f r) : r.length < s.length :=
  (family_length s.length s (Nat.le_refl _)).2.1 h

/--
An object's members never lengthen what is left. It is the object counterpart of the bound on an
array's elements, and needed separately because `Members` is a distinct production over a distinct
kind of contents.

`h : Members s ms r` says the front of `s` is one or more members separated by commas, yielding
`ms`. `r.length ≤ s.length` is `family_length` taken at `n := s.length`. As with `Member`, a
strict bound would hold but is not what the callers ask for.
-/
theorem members_length {s : List Char} {ms : List (String × Json)} {r : List Char}
    (h : Members s ms r) : r.length ≤ s.length :=
  (family_length s.length s (Nat.le_refl _)).2.2.2.2.2 h

/--
A value consumes at least one character. This is the bound the whole grammar turns on: it is what
lets an induction on the length of the text reach inside a nested value, and it is what makes a
list of values shorten the text as it is walked.

`h : Value s j r` says the front of `s` is a `value` production denoting `j`, and
`r.length < s.length` holds for all seven alternatives: the literals cost four or five characters,
the containers two brackets, and the numbers and strings at least one, by `num_length` and
`str_length`. It is `family_length` taken at `n := s.length`.
-/
theorem value_length {s : List Char} {j : Json} {r : List Char} (h : Value s j r) :
    r.length < s.length := (family_length s.length s (Nat.le_refl _)).2.2.1 h

/--
An array's elements never lengthen what is left. The claim is deliberately non-strict, which is
all any use of it asks for, though `Elements` has no empty derivation and so does in fact consume.

`h : Elements s vs r` says the front of `s` is one or more values separated by commas, denoting
`vs`. `r.length ≤ s.length` is `family_length` taken at `n := s.length`. The strict version
would follow from `value_length` at the head of the list, but it is not stated because nothing
needs it.
-/
theorem elements_length {s : List Char} {vs : List Json} {r : List Char}
    (h : Elements s vs r) : r.length ≤ s.length :=
  (family_length s.length s (Nat.le_refl _)).2.2.2.1 h

/--
One member of an object never lengthens what is left. A member is a name, a colon and a value, so
more than this holds; the weaker form is what the surrounding proofs are written against, and it
is enough for them.

`h : Member s m r` says the front of `s` is a `member` production yielding the pair `m`.
`r.length ≤ s.length` is `family_length` taken at `n := s.length`; `str_length` and
`token_length` would sharpen it, but the sharper bound is not used.
-/
theorem member_length {s : List Char} {m : String × Json} {r : List Char}
    (h : Member s m r) : r.length ≤ s.length :=
  (family_length s.length s (Nat.le_refl _)).2.2.2.2.1 h

end Json.Spec
