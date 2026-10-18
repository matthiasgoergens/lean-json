/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Printer
public import Json.Spec

public section

namespace Json.Printer

/-!
What the printer emits, stated against the grammar rather than against the printer.

The printer runs over an explicit stack, which is what keeps it safe on deep values but leaves
its output related to the value only through a loop invariant. So the text is described a second
time by structural recursion, `chars`, and the two are proved to agree; the grammar theorems are
then stated about `chars`, where induction follows the shape of the value. Only the claims a
caller can use are exported; the description and the per-production lemmas are the scaffolding
that reaches them.
-/

/-! ## The same output, described by recursion on the value -/

mutual

private def chars (st : Style) (depth : Nat) : Json → List Char
  | .null => "null".toList
  | .bool true => "true".toList
  | .bool false => "false".toList
  | .num n => (number n).toList
  | .str s => (string s).toList
  | .arr elems =>
    if elems.isEmpty then "[]".toList
    else ("[" ++ st.lineBreak (depth + 1)).toList ++ elemChars st (depth + 1) elems.toList true ++
      (st.lineBreak depth ++ "]").toList
  | .obj fields =>
    if fields.isEmpty then "{}".toList
    else ("{" ++ st.lineBreak (depth + 1)).toList ++
      memberChars st (depth + 1) fields.toList true ++ (st.lineBreak depth ++ "}").toList

private def elemChars (st : Style) (depth : Nat) : List Json → Bool → List Char
  | [], _ => []
  | j :: l, first =>
    (st.precedes depth first).toList ++ chars st depth j ++ elemChars st depth l false

private def memberChars (st : Style) (depth : Nat) : List (String × Json) → Bool → List Char
  | [], _ => []
  | (k, v) :: l, first =>
    (st.precedes depth first).toList ++ (string k).toList ++ st.colon.toList ++
      chars st depth v ++ memberChars st depth l false

end

private def itemChars (st : Style) : Item → List Char
  | .lit s => s.toList
  | .val d j => chars st d j
  | .elems d l first => elemChars st d l first
  | .members d l first => memberChars st d l first

private def itemsChars (st : Style) : List Item → List Char
  | [] => []
  | i :: rest => itemChars st i ++ itemsChars st rest

/-! ## Agreement -/

/-- The characters a string contributes inside a literal. -/
private def escapeCharsOf (l : List Char) : List Char := (l.map escapeChars).flatten

/--
Escaping one character onto an accumulator appends exactly the characters the recursive
description says it does. The printer escapes by pushing onto a `String` while every grammar
theorem is stated over lists of characters, so the two spellings of an escape have to be
identified before anything at all can be said about the output.

`escapeCharTo acc c` is the accumulating form and `escapeChars c` the list form. The equation says
the accumulator is left alone and the escape appended, for every character. It covers the `\u00XX`
branch as well as the named ones, and that is where it has content: there the two forms are
written differently, one pushing characters onto a string and the other producing a six element
list.
-/
private theorem toList_escapeCharTo (acc : String) (c : Char) :
    (escapeCharTo acc c).toList = acc.toList ++ escapeChars c := by
  fun_cases escapeCharTo acc c <;> simp [escapeChars] <;> omega

/--
Escaping a whole list of characters onto an accumulator appends the concatenation of their
escapes. It lifts the single-character claim to the fold the printer actually runs over a string.

`l.foldl escapeCharTo acc` escapes each character in turn, and `escapeCharsOf l` is the
concatenation of the individual escapes. The equation is stated for an arbitrary accumulator,
generalised in the induction, which is what makes each step usable; fixed at the accumulator the
fold began with, the hypothesis would not apply after the first character.
-/
private theorem toList_foldl_escape (l : List Char) (acc : String) :
    (l.foldl escapeCharTo acc).toList = acc.toList ++ escapeCharsOf l := by
  induction l generalizing acc with
  | nil => simp [escapeCharsOf]
  | cons c cs ih => simp [ih, toList_escapeCharTo, escapeCharsOf]

/--
Escaping a `String` onto an accumulator appends the concatenation of its characters' escapes. The
printer works over `String`s and the description over lists, and this is where the two are joined
for the body of a literal.

`escapeTo acc s` folds over the characters of `s`, and the equation gives the result as
`acc.toList ++ escapeCharsOf s.toList`. It is `toList_foldl_escape` composed with
`String.foldl_eq_foldl_toList`, which is what says folding a string is folding its characters.
-/
private theorem toList_escapeTo (acc s : String) :
    (escapeTo acc s).toList = acc.toList ++ escapeCharsOf s.toList := by
  simp [escapeTo, String.foldl_eq_foldl_toList, toList_foldl_escape]

/--
A rendered string literal is a quotation mark, the escaped body, and a quotation mark. That is the
shape `Spec.Str` expects, so every claim about a printed string has to be reduced to it.

`(string s).toList = '"' :: (escapeCharsOf s.toList ++ ['"'])` writes both quotation marks
explicitly and gives the body as the concatenation of the per-character escapes, which is what
`spec_chars` is stated about. Nothing is required of `s`: every string, whatever characters it
holds, is rendered in this shape.
-/
private theorem toList_string (s : String) :
    (string s).toList = '"' :: (escapeCharsOf s.toList ++ ['"']) := by
  simp [string, stringTo, String.toList_push, toList_escapeTo]

/--
Rendering a string onto an accumulator appends the whole literal to it. The printer's traversal
accumulates into one `String`, so a member name or a string value has to be seen as an untouched
prefix followed by a complete literal.

`(stringTo acc s).toList = acc.toList ++ (string s).toList`. The accumulator being untouched is
what lets an induction over the printer's item stack peel one item at a time, and the appended
part is the literal `toList_string` describes.
-/
private theorem toList_stringTo (acc s : String) :
    (stringTo acc s).toList = acc.toList ++ (string s).toList := by
  simp [stringTo, String.toList_push, toList_escapeTo, toList_string]

/-! ## Digits -/

/-- The value a run of digit characters denotes. -/
private def digitsValue : List Char → Nat
  | [] => 0
  | c :: cs => Spec.digitVal c * 10 ^ cs.length + digitsValue cs

/--
The value of two runs of digits written one after the other is the first shifted by the length of
the second, plus the second. Digits are produced by appending, most significant first, so every
claim about what a printed number denotes has to cross a concatenation.

`digitsValue` reads a list of digit characters most significant first. In
`digitsValue (l₁ ++ l₂) = digitsValue l₁ * 10 ^ l₂.length + digitsValue l₂` the shift is
by the number of digits in `l₂` and by nothing about their values, which is what makes it usable
for a run of padding zeros. The induction is on `l₁`.
-/
private theorem digitsValue_append (l₁ l₂ : List Char) :
    digitsValue (l₁ ++ l₂) = digitsValue l₁ * 10 ^ l₂.length + digitsValue l₂ := by
  induction l₁ with
  | nil => simp [digitsValue]
  | cons c cs ih =>
    simp only [List.cons_append, digitsValue, ih, List.length_append, Nat.pow_add,
      Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/--
The grammar reads back the hexadecimal digit the printer writes. A control character is escaped as
`\u00XX`, so the two nibbles the printer emits have to be exactly what `Hex4` will decode.

`h : d < 16` confines `d` to the sixteen digits, which is what makes the claim a finite check: it
is settled by `decide` over `List.range 16` and then instantiated at `d`. Without the bound
`hexDigitChar` would be applied outside the range it is written for and the equation would fail.
-/
private theorem hexVal_hexDigitChar {d : Nat} (h : d < 16) :
    Spec.hexVal? (hexDigitChar d) = some d :=
  (by decide : ∀ d ∈ List.range 16, Spec.hexVal? (hexDigitChar d) = some d) d
    (List.mem_range.mpr h)

/--
The character the printer writes for a digit is one the grammar recognises as a digit. Numbers are
written by mapping values to characters while the grammar's `DIGIT` is a range of characters, so
the two have to be connected somewhere, and this is where.

`h : d < 10` confines `d` to the ten digits and makes the claim a finite check, run by `decide`
over `List.range 10`. It says only that the character is a digit and nothing about which one; that
is the next claim's business.
-/
private theorem isDigit_digitChar {d : Nat} (h : d < 10) : Spec.isDigit (digitChar d) = true :=
  (by decide : ∀ d ∈ List.range 10, Spec.isDigit (digitChar d) = true) d (List.mem_range.mpr h)

/--
The grammar reads back the value of the digit the printer wrote. With the previous claim this
makes the digit characters a faithful encoding, which is what a printed number denoting the right
value ultimately rests on.

`h : d < 10` again makes the check finite, over `List.range 10`. `Spec.digitVal (digitChar d) = d`
says the round trip is the identity on the ten digits. The bound is essential: applied to a larger
argument `digitChar` produces a character outside `'0'` to `'9'`, which `digitVal` does not
invert.
-/
private theorem digitVal_digitChar {d : Nat} (h : d < 10) : Spec.digitVal (digitChar d) = d :=
  (by decide : ∀ d ∈ List.range 10, Spec.digitVal (digitChar d) = d) d (List.mem_range.mpr h)

/--
The accumulating digit renderer prepends a number's digits to whatever it was given. Everything
below reasons about `digitChars`, the accumulator-free form, so each appearance of the
accumulating one has to be rewritten into it first.

`digitCharsTo n acc = digitChars n ++ acc` holds for every accumulator, which is what makes it an
induction hypothesis. The induction is strong recursion on `n`, following the division by ten, and
the accumulator changes at every step, which is why it cannot be fixed.
-/
private theorem digitCharsTo_eq (n : Nat) : ∀ acc, digitCharsTo n acc = digitChars n ++ acc := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    by_cases h : n < 10
    · rw [digitCharsTo, ite_eq_left h, digitChars, digitCharsTo, ite_eq_left h]
      simp
    · have hr : digitChars n = digitCharsTo (n / 10) [digitChar (n % 10)] := by
        rw [digitChars, digitCharsTo, ite_eq_right h]
      rw [digitCharsTo, ite_eq_right h, hr, ih (n / 10) (by omega), ih (n / 10) (by omega)]
      simp

/--
A single-digit number is written as one character. It is the base case of every induction over the
digits of a number, and it is what fixes zero as `'0'` rather than as nothing.

`h : n < 10` selects the non-recursive branch, and `digitChars n = [digitChar n]` gives the
one-element list. Above ten the equation is false, the rendering then having more than one
character, so the hypothesis is doing real work.
-/
private theorem digitChars_of_lt {n : Nat} (h : n < 10) : digitChars n = [digitChar n] := by
  rw [digitChars, digitCharsTo, ite_eq_left h]

/--
A number of two digits or more is written as its leading digits followed by its last. This is the
step of every induction over the digits, and it is what puts the least significant digit at the
end, where `digitsValue` expects to find it.

`h : 10 ≤ n` selects the recursive branch, and the conclusion splits the rendering into
`digitChars (n / 10)` and `[digitChar (n % 10)]`. The hypothesis is what stops the split being
applied to a single digit, where `n / 10` is zero and the left part would be a spurious `'0'`.
-/
private theorem digitChars_of_le {n : Nat} (h : 10 ≤ n) :
    digitChars n = digitChars (n / 10) ++ [digitChar (n % 10)] := by
  rw [digitChars, digitCharsTo, ite_eq_right (by omega), digitCharsTo_eq]

/--
Every number is written as at least one character. The grammar's `1*DIGIT` requires a digit, so a
rendering that could be empty would derive nothing at all.

`digitChars n ≠ []` holds for every natural number, zero included, which is written as `'0'`.
The two cases follow the two equations above, one giving a singleton and the other a list that
ends in a digit; neither can be empty.
-/
private theorem digitChars_ne_nil (n : Nat) : digitChars n ≠ [] := by
  by_cases h : n < 10
  · simp [digitChars_of_lt h]
  · simp [digitChars_of_le (show 10 ≤ n by omega)]

/--
Every character a number is written with is a digit. `Spec.Digits` demands this of each character
of the run, so it has to hold throughout the rendering and not merely at its head.

The claim quantifies over the members of `digitChars n`, covering the leading digit and every
later one alike. The induction is strong recursion on `n`: the single-digit case is
`isDigit_digitChar`, and the recursive case splits the rendering with `digitChars_of_le` and
handles the last digit separately.
-/
private theorem isDigit_of_mem_digitChars (n : Nat) :
    ∀ c ∈ digitChars n, Spec.isDigit c = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · simp only [digitChars_of_lt h, List.mem_singleton]
      intro c hc
      exact hc ▸ isDigit_digitChar h
    · simp only [digitChars_of_le (by omega : 10 ≤ n), List.mem_append, List.mem_singleton]
      intro c hc
      rcases hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · exact hc ▸ isDigit_digitChar (by omega)

/--
A number written out and read back is the number it was. This is what makes the printer's output
denote what it came from, and every claim the number soundness proof makes about values passes
through it.

`digitsValue (digitChars n) = n` holds for every natural number, zero included. The recursive case
splits off the last digit with `digitsValue_append`, evaluates it with `digitVal_digitChar`, and
takes the rest from the induction hypothesis; reassembling `n / 10 * 10 + n % 10` into `n` is the
arithmetic `omega` closes.
-/
private theorem digitsValue_digitChars (n : Nat) : digitsValue (digitChars n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · simp [digitChars_of_lt h, digitsValue, digitVal_digitChar h]
    · rw [digitChars_of_le (by omega : 10 ≤ n), digitsValue_append,
        ih (n / 10) (by omega)]
      simp [digitsValue, digitVal_digitChar (show n % 10 < 10 by omega)]
      omega

/--
A non-zero number is written with a leading digit between `1` and `9`. The grammar's `int` forbids
a leading zero on anything but the single character `0`, so without this the printer's mantissa
could not be derived at all.

`h : 1 ≤ n` excludes zero, whose rendering begins with `'0'` and would make the claim false. The
conclusion produces the head and tail of the rendering together with the range condition, in
exactly the shape `Spec.Int'.digits` asks for. The induction is on `n`, and the leading digit
survives the appending of later digits, so it comes from the innermost step.
-/
private theorem head_digitChars {n : Nat} (h : 1 ≤ n) :
    ∃ c cs, digitChars n = c :: cs ∧ ('1' ≤ c && c ≤ '9') = true := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases hlt : n < 10
    · refine ⟨digitChar n, [], digitChars_of_lt hlt, ?_⟩
      exact (by decide : ∀ d ∈ List.range' 1 9, ('1' ≤ digitChar d && digitChar d ≤ '9') = true) n
        (List.mem_range'_1.mpr ⟨h, by omega⟩)
    · obtain ⟨c, cs, hc, hrange⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨c, cs ++ [digitChar (n % 10)], by
        rw [digitChars_of_le (by omega : 10 ≤ n), hc, List.cons_append], hrange⟩

/--
A non-empty list of digit characters derives as `1*DIGIT`, denoting the value it spells and
counting its own length. This is where the printer's output first meets the grammar, and every one
of the number productions is built on it.

`hd` requires every character to be a digit and `hne` requires the list to be non-empty, `Digits`
having no empty derivation. `Spec.Digits (l ++ r) (digitsValue l) l.length r` says the run
consumes exactly `l` and leaves `r`, which is arbitrary and so may be anything the number is
followed by. The value recorded is what `digitsValue` reads and the count is the list's length.
The induction is on `l`, the one-element case being `Digits.last`.
-/
private theorem spec_digits {l : List Char} (hd : ∀ c ∈ l, Spec.isDigit c = true) (hne : l ≠ [])
    (r : List Char) : Spec.Digits (l ++ r) (digitsValue l) l.length r := by
  induction l with
  | nil => exact absurd rfl hne
  | cons c cs ih =>
    match cs with
    | [] => simpa [digitsValue] using Spec.Digits.last (r := r) (hd c (by simp))
    | c' :: cs' =>
      exact Spec.Digits.cons (hd c (by simp))
        (ih (fun x hx => hd x (by simp [hx])) (by simp))

/--
Appending to a non-empty list leaves it non-empty. It is used where a run of digits is assembled
from two parts and only the second of them is known to be non-empty.

`h : l₂ ≠ []` is the hypothesis and `l₁ ++ l₂ ≠ []` the conclusion; nothing is required
of `l₁`, which may itself be empty. It is settled by cases on `l₁`.
-/
private theorem append_ne_nil_of_right {l₁ l₂ : List Char} (h : l₂ ≠ []) : l₁ ++ l₂ ≠ [] := by
  cases l₁ <;> simp_all

/--
Two runs of digit characters, concatenated, derive as one `1*DIGIT` denoting the combined value.
The printer writes a mantissa and its padding zeros as separate pieces, so the derivation has to
be assembled across the join between them.

`h₁` and `h₂` require the characters of each part to be digits, and `hne` requires only the
concatenation to be non-empty, so either part alone may be empty. The value recorded,
`digitsValue l₁ * 10 ^ l₂.length + digitsValue l₂`, is `digitsValue_append` written out, and
the count is the sum of the two lengths. It is `spec_digits` at the concatenation, re-associated
so that the remainder sits outside both parts.
-/
private theorem spec_digits_append {l₁ l₂ r : List Char}
    (h₁ : ∀ c ∈ l₁, Spec.isDigit c = true) (h₂ : ∀ c ∈ l₂, Spec.isDigit c = true)
    (hne : l₁ ++ l₂ ≠ []) :
    Spec.Digits (l₁ ++ (l₂ ++ r)) (digitsValue l₁ * 10 ^ l₂.length + digitsValue l₂)
      (l₁.length + l₂.length) r := by
  have h := spec_digits (l := l₁ ++ l₂)
    (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · exact h₁ c h
      · exact h₂ c h) hne r
  rw [List.append_assoc] at h
  simpa [digitsValue_append] using h

/--
A list of digit characters whose first is not zero derives as `int`. The grammar keeps a leading
zero for the single character `0` alone, so a printed mantissa can only be derived when its first
digit is something else.

`hd` requires every character to be a digit, and `hhead` produces the head with
`'1' ≤ c ∧ c ≤ '9'`, which is exactly the side condition of `Int'.digits`. The conclusion
consumes `l`, leaves an arbitrary `r`, and records `digitsValue l`. The `zero` constructor is not
reached here; a zero mantissa is written and derived separately in `spec_num`.
-/
private theorem spec_int' {l : List Char} (hd : ∀ c ∈ l, Spec.isDigit c = true)
    (hhead : ∃ c cs, l = c :: cs ∧ ('1' ≤ c && c ≤ '9') = true) (r : List Char) :
    Spec.Int' (l ++ r) (digitsValue l) r := by
  obtain ⟨c, cs, hl, hrange⟩ := hhead
  subst hl
  exact Spec.Int'.digits hrange (spec_digits hd (by simp) r)

/--
The padding the printer writes is made of digits. Trailing zeros are appended to a mantissa in
order to write a number plainly, and they have to satisfy the same condition the mantissa's own
characters do.

The claim quantifies over the members of `List.replicate k '0'`, of which there is only `'0'`, so
it reduces by `List.eq_of_mem_replicate` to a single `decide`. It holds at `k = 0`, where there is
nothing to check, which is the case where no padding was written.
-/
private theorem isDigit_of_mem_zeros (k : Nat) :
    ∀ c ∈ List.replicate k '0', Spec.isDigit c = true := by
  intro c hc
  rw [List.eq_of_mem_replicate hc]
  decide

/--
A run of zeros denotes zero. The padding contributes to a number's value only by shifting the
mantissa, never by adding to it, and this is the half of that concerning what it adds.

`digitsValue (List.replicate k '0') = 0` for every `k`. The induction is on `k`, each step
contributing `Spec.digitVal '0'`, which is zero, multiplied by a power of ten. The shift the
padding does contribute is accounted for by the `l₂.length` of `digitsValue_append`, not here.
-/
private theorem digitsValue_zeros (k : Nat) : digitsValue (List.replicate k '0') = 0 := by
  induction k with
  | zero => simp [digitsValue]
  | succ k ih => simp [List.replicate_succ, digitsValue, ih, Spec.digitVal]

/-! ## Numbers -/

/--
The sign the printer writes is a single minus or nothing at all. It is chosen by a conditional
between two `String`s, and `Spec.Sign` expects a list, so the conditional has to be pushed through
the conversion before the two can be matched.

The equation moves `toList` inside the `if`: a negative mantissa gives `['-']` and anything else
the empty list. It is proved by cases on `m < 0`, and both branches are needed, `spec_num_of`
splitting on that same condition.
-/
private theorem toList_sign (m : Int) :
    ((if m < 0 then "-" else "" : String)).toList = (if m < 0 then ['-'] else []) := by
  by_cases h : m < 0 <;> simp [h]

/--
Multiplying a mantissa by a power of ten and dropping the exponent leaves the normal form alone.
The printer writes a small positive exponent as trailing zeros, so the number the grammar reads
back carries in its mantissa what the original carried in its exponent, and the two have to
normalise to the same thing.

`Number.normalize (m * 10 ^ k) 0 = Number.normalize m k` is an equality of `Number`s. It follows
from `Number.eqv_iff_normalize_eq` once `⟨m * 10 ^ k, 0⟩` and `⟨m, k⟩` are shown
equivalent, which is a rescaling to their common exponent `min 0 k`, computed directly here. `k`
is a natural number, so the shift is a multiplication and never a division.
-/
private theorem normalize_mul_pow (m : Int) (k : Nat) :
    Number.normalize (m * 10 ^ k) 0 = Number.normalize m k :=
  Number.eqv_iff_normalize_eq.mp <| by
    show Number.Eqv ⟨m * 10 ^ k, 0⟩ ⟨m, (k : Int)⟩
    have h : ((k : Int) - min 0 (k : Int)).toNat = k := by omega
    have h0 : ((0 : Int) - min 0 (k : Int)).toNat = 0 := by omega
    simp only [Number.Eqv, Number.scaleTo, h, h0, Int.pow_zero, Int.mul_one]

/--
A sign followed by the four number productions is a `number`, whichever way the sign went. Every
branch of the printer's number rendering has this shape, so factoring it out is what keeps six
branches from repeating the same assembly six times.

`hi`, `hf` and `he` are the integer, fraction and exponent derivations, threaded through the
intermediate texts `s₂` and `s₃`, and `hv` says the value they compute is the target. The
conclusion prefixes `['-']` or `[]` according to `m < 0`, matching the sign recorded in the value.
`m` appears only in that conditional and need not be the mantissa of anything, which is what lets
the caller supply the same condition the printer branched on.
-/
private theorem spec_num_of {m : Int} {text r s₂ s₃ : List Char} {i f nf : Nat} {e : Int}
    {target : Number}
    (hi : Spec.Int' text i s₂) (hf : Spec.Frac s₂ f nf s₃) (he : Spec.Exp s₃ e r)
    (hv : Number.normalize
      (if m < 0 then -((i * 10 ^ nf + f : Nat) : Int) else ((i * 10 ^ nf + f : Nat) : Int))
      (e - nf) = target) :
    Spec.Num ((if m < 0 then ['-'] else []) ++ text) target r := by
  subst hv
  by_cases h : m < 0
  · simpa [h] using Spec.Num.mk (neg := true) Spec.Sign.minus hi hf he
  · simpa [h] using Spec.Num.mk (neg := false) Spec.Sign.absent hi hf he

/--
What the printer writes for a number is a `number` in the grammar's sense, denoting that number's
normal form. It is the hardest of the leaf claims, the printer having six ways to write a number,
and the value case for numbers rests entirely on it.

`Spec.Num ((number n).toList ++ r) (Number.normalize n.mantissa n.exponent) r` says the rendering
is consumed exactly and an arbitrary `r` left. The normal form appears rather than `n` itself
because the grammar records what the digits denote in canonical form; where `n` is canonical the
two coincide, which is what `spec_value` relies on. The branches are a zero mantissa, written `0`;
a zero exponent; a small positive exponent written as padding, where `normalize_mul_pow` moves the
shift from the exponent into the mantissa; a large positive exponent written with `e`; a negative
exponent falling inside the mantissa's digits, written with a decimal point; and a negative
exponent beyond them, written either as `0.` with zeros or with `e-`.
-/
private theorem spec_num (n : Number) (r : List Char) :
    Spec.Num ((number n).toList ++ r) (Number.normalize n.mantissa n.exponent) r := by
  by_cases hm : n.mantissa = 0
  · simp only [number, ite_eq_left hm]
    have hz : Number.normalize n.mantissa n.exponent = Number.normalize 0 0 := by
      simp [Number.normalize, hm]
    rw [hz]
    simpa using Spec.Num.mk (neg := false) (s₁ := '0' :: r) Spec.Sign.absent Spec.Int'.zero
      Spec.Frac.absent Spec.Exp.absent
  · have hd := isDigit_of_mem_digitChars n.mantissa.natAbs
    have hval := digitsValue_digitChars n.mantissa.natAbs
    have hhead := head_digitChars (show 1 ≤ n.mantissa.natAbs by omega)
    simp only [number, ite_eq_right hm]
    by_cases he0 : n.exponent = 0
    · rw [ite_eq_left he0]
      simp only [String.toList_append, String.toList_ofList, toList_sign, List.append_assoc]
      refine spec_num_of (hval ▸ spec_int' hd hhead r) Spec.Frac.absent Spec.Exp.absent ?_
      rw [he0]
      simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
      congr 1
      omega
    · have hsign : (if n.mantissa < 0 then -((n.mantissa.natAbs : Int))
          else ((n.mantissa.natAbs : Int))) = n.mantissa := by
        by_cases h : n.mantissa < 0 <;> simp only [h, ite_true, ite_false] <;> omega
      rw [ite_eq_right he0]
      by_cases hpos : 0 < n.exponent
      · rw [ite_eq_left hpos]
        by_cases hlim : n.exponent ≤ (plainZeroLimit : Int)
        · -- Plain decimal with trailing zeros: the padding belongs to the integer part.
          rw [ite_eq_left hlim]
          simp only [String.toList_append, String.toList_ofList, toList_sign, zeros,
            List.append_assoc]
          obtain ⟨c, cs, hc, hrange⟩ := hhead
          have hi := spec_int'
            (l := digitChars n.mantissa.natAbs ++ List.replicate n.exponent.toNat '0')
            (fun x hx => by
              rcases List.mem_append.mp hx with h | h
              · exact isDigit_of_mem_digitChars _ x h
              · exact isDigit_of_mem_zeros _ x h)
            ⟨c, cs ++ List.replicate n.exponent.toNat '0', by rw [hc, List.cons_append],
              hrange⟩ r
          rw [List.append_assoc, digitsValue_append, hval, digitsValue_zeros, Nat.add_zero,
            List.length_replicate] at hi
          refine spec_num_of hi Spec.Frac.absent Spec.Exp.absent ?_
          simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
          have hcast : (if n.mantissa < 0
              then -((n.mantissa.natAbs * 10 ^ n.exponent.toNat : Nat) : Int)
              else ((n.mantissa.natAbs * 10 ^ n.exponent.toNat : Nat) : Int))
              = n.mantissa * 10 ^ n.exponent.toNat := by
            by_cases h : n.mantissa < 0
            · simp only [ite_eq_left h, Int.natCast_mul, Int.natCast_pow, ← Int.neg_mul]
              congr 1
              omega
            · simp only [ite_eq_right h, Int.natCast_mul, Int.natCast_pow]
              congr 1
              omega
          rw [hcast, show ((0 : Int) - ((0 : Nat) : Int)) = 0 from by omega, normalize_mul_pow]
          congr 1
          omega
        · -- Exponent notation, the padding being too long to write out.
          rw [ite_eq_right hlim, ite_eq_right (show ¬n.exponent < 0 by omega)]
          simp only [String.toList_append, String.toList_ofList, toList_sign, digitString,
            List.append_assoc]
          refine spec_num_of (hval ▸ spec_int' hd hhead _) Spec.Frac.absent
            (Spec.Exp.bare (Or.inl rfl)
              ((digitsValue_digitChars n.exponent.toNat) ▸
                spec_digits (isDigit_of_mem_digitChars _) (digitChars_ne_nil _) r)) ?_
          simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
          rw [hsign]
          congr 1
          omega
      · by_cases hk : (-n.exponent).toNat < (digitChars n.mantissa.natAbs).length
        · -- A decimal point inside the digits.
          rw [ite_eq_right hpos, ite_eq_left hk]
          simp only [String.toList_append, String.toList_ofList, toList_sign, List.append_assoc]
          obtain ⟨c, cs, hc, hrange⟩ := hhead
          obtain ⟨j, hjdef⟩ : ∃ j, (digitChars n.mantissa.natAbs).length -
              (-n.exponent).toNat = j + 1 :=
            ⟨(digitChars n.mantissa.natAbs).length - (-n.exponent).toNat - 1, by omega⟩
          rw [hjdef]
          have htake : (digitChars n.mantissa.natAbs).take (j + 1) = c :: cs.take j := by
            rw [hc, List.take_succ_cons]
          have hdroplen : ((digitChars n.mantissa.natAbs).drop (j + 1)).length =
              (-n.exponent).toNat := by
            rw [List.length_drop]
            omega
          have hi := spec_int' (l := (digitChars n.mantissa.natAbs).take (j + 1))
            (fun x hx => isDigit_of_mem_digitChars _ x (List.mem_of_mem_take hx))
            ⟨c, _, htake, hrange⟩
            ('.' :: ((digitChars n.mantissa.natAbs).drop (j + 1) ++ r))
          refine spec_num_of hi
            (Spec.Frac.present (spec_digits
              (fun x hx => isDigit_of_mem_digitChars _ x (List.mem_of_mem_drop hx))
              (by simp only [ne_eq, List.eq_nil_iff_length_eq_zero, hdroplen]; omega) r))
            Spec.Exp.absent ?_
          rw [hdroplen, show digitsValue ((digitChars n.mantissa.natAbs).take (j + 1)) *
              10 ^ (-n.exponent).toNat +
              digitsValue ((digitChars n.mantissa.natAbs).drop (j + 1)) = n.mantissa.natAbs from by
            rw [← hdroplen, ← digitsValue_append, List.take_append_drop, hval], hsign]
          congr 1
          omega
        · by_cases hz : (-n.exponent).toNat - (digitChars n.mantissa.natAbs).length
              ≤ plainZeroLimit
          · -- A zero integer part, and a fraction that starts with padding.
            rw [ite_eq_right hpos, ite_eq_right hk, ite_eq_left hz]
            simp only [String.toList_append, String.toList_ofList, toList_sign, zeros,
              List.append_assoc]
            refine spec_num_of Spec.Int'.zero
              (Spec.Frac.present (spec_digits_append
                (l₁ := List.replicate ((-n.exponent).toNat -
                  (digitChars n.mantissa.natAbs).length) '0')
                (l₂ := digitChars n.mantissa.natAbs)
                (isDigit_of_mem_zeros _) (isDigit_of_mem_digitChars _)
                (append_ne_nil_of_right (digitChars_ne_nil _)))) Spec.Exp.absent ?_
            rw [digitsValue_zeros, hval, List.length_replicate, Nat.zero_mul, Nat.zero_add,
              Nat.zero_mul, Nat.zero_add,
              show (-n.exponent).toNat - (digitChars n.mantissa.natAbs).length +
                (digitChars n.mantissa.natAbs).length = (-n.exponent).toNat from by omega,
              hsign]
            congr 1
            omega
          · -- Exponent notation again, this time with a negative exponent.
            rw [ite_eq_right hpos, ite_eq_right hk, ite_eq_right hz, ite_eq_left (show n.exponent < 0 by omega)]
            simp only [String.toList_append, String.toList_ofList, toList_sign, digitString,
              List.append_assoc]
            refine spec_num_of (hval ▸ spec_int' hd hhead _) Spec.Frac.absent
              (Spec.Exp.minus (Or.inl rfl)
                ((digitsValue_digitChars (-n.exponent).toNat) ▸
                  spec_digits (isDigit_of_mem_digitChars _) (digitChars_ne_nil _) r)) ?_
            simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero]
            rw [hsign]
            congr 1
            omega

/-! ## Strings -/

/--
What the printer writes for one character is a `char` in the grammar's sense, denoting that
character. The escapes and the unescaped case have to be covered together, the printer choosing
between them by a condition the grammar states in quite another way.

`Spec.Ch (escapeChars c ++ r) c r` consumes the escape and leaves an arbitrary `r`. The named
escapes map onto their constructors directly. The `\u00XX` branch builds `Hex4` from
`hexVal_hexDigitChar` on the two nibbles, with zeros for the two leading digits. The last branch
is the unescaped one, and there what has to be shown is that a character which is neither `"` nor
`\` nor a control character satisfies `isUnescaped`, which is arithmetic on its code point.
-/
private theorem spec_ch (c : Char) (r : List Char) : Spec.Ch (escapeChars c ++ r) c r := by
  fun_cases escapeChars c
  case case1 => exact .quote
  case case2 => exact .backslash
  case case3 => exact .backspace
  case case4 => exact .formFeed
  case case5 => exact .lineFeed
  case case6 => exact .carriageReturn
  case case7 => exact .tab
  case case8 =>
    rename_i hctrl
    refine Spec.Ch.codePoint (v := 0 * 4096 + 0 * 256 + c.toNat / 16 * 16 + c.toNat % 16)
      (Spec.Hex4.mk (by decide) (by decide) (hexVal_hexDigitChar (by omega))
        (hexVal_hexDigitChar (by omega))) (by omega)
  case case9 =>
    rename_i h1 h2 _ _ _ _ _ _
    refine Spec.Ch.unescaped ?_
    have h34 : c.toNat ≠ 34 := fun h => h1 (Char.toNat_inj.mp (by rw [h]; rfl))
    have h92 : c.toNat ≠ 92 := fun h => h2 (Char.toNat_inj.mp (by rw [h]; rfl))
    simp only [Spec.isUnescaped, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega

/--
What the printer writes for a list of characters is a `*char` run denoting that list. It is the
body of a string literal, and it is where the single-character claim is repeated along the whole
string.

`Spec.Chars (escapeCharsOf l ++ r) l r` says the concatenated escapes are consumed and the
original characters recovered in order, leaving an arbitrary `r`. The induction is on `l`, with
`spec_ch` at each step and `Chars.nil` at the empty list, which is the empty string's body.
-/
private theorem spec_chars (l r : List Char) : Spec.Chars (escapeCharsOf l ++ r) l r := by
  induction l with
  | nil => simpa [escapeCharsOf] using Spec.Chars.nil (r := r)
  | cons c cs ih =>
    have h := Spec.Chars.cons (spec_ch c (escapeCharsOf cs ++ r)) ih
    simpa [escapeCharsOf, List.append_assoc] using h

/--
What the printer writes for a string is a `string` in the grammar's sense, denoting that string.
It holds of every string, one carrying control characters or characters outside the basic plane
included, the escaping having already been accounted for.

`Spec.Str ((string s).toList ++ r) s r` consumes the whole literal and leaves an arbitrary `r`.
`toList_string` puts the rendering into the shape `Str.mk` wants, both quotation marks included,
and `spec_chars` supplies the body; `String.ofList_toList` is what turns the recovered list of
characters back into `s` itself rather than into something merely equal to it character by
character.
-/
private theorem spec_str (s : String) (r : List Char) : Spec.Str ((string s).toList ++ r) s r := by
  rw [toList_string]
  have h := Spec.Str.mk (spec_chars s.toList ('"' :: r))
  rw [String.ofList_toList] at h
  simpa using h

/-! ## Whitespace and structural characters -/

/--
A run of spaces is whitespace. Indentation is written as spaces, and the grammar has to be shown
to skip exactly them and to stop where they stop.

`Spec.Ws ((spaces n).toList ++ x) x` says the `n` spaces are consumed and `x` left untouched,
whatever `x` is. The induction is on `n`, each step being `Ws.cons` with `decide` supplying
`isWs ' '`; at `n = 0` it is `Ws.nil`, which is the compact style's case.
-/
private theorem ws_spaces (n : Nat) (x : List Char) : Spec.Ws ((spaces n).toList ++ x) x := by
  simp only [spaces, String.toList_ofList]
  induction n with
  | zero => simpa using Spec.Ws.nil (r := x)
  | succ n ih => exact List.replicate_succ ▸ Spec.Ws.cons (by decide) ih

/--
What the layout writes before an item is whitespace. In the compact style that is nothing and in
the indented style a newline and some spaces, and the text derives only if both count as
whitespace.

`Spec.Ws ((st.lineBreak d).toList ++ x) x` says the break is consumed and `x` left. The compact
case is `Ws.nil`, the string being empty; the indented case is `Ws.cons` for the newline followed
by `ws_spaces` for the indentation. The depth `d` changes only how many spaces there are.
-/
private theorem ws_lineBreak (st : Style) (d : Nat) (x : List Char) :
    Spec.Ws ((st.lineBreak d).toList ++ x) x := by
  unfold Style.lineBreak
  split
  · simpa using Spec.Ws.nil (r := x)
  · simpa [String.toList_append] using Spec.Ws.cons (c := '\n') (by decide) (ws_spaces _ x)

/--
An opening or separating character followed by a line break is a token in the grammar's sense.
This layout never puts space before such a character, so its leading whitespace is empty and its
trailing whitespace is the break.

`Spec.Token t (t :: ((st.lineBreak d).toList ++ x)) x` is built from `Ws.nil` for the leading run
and `ws_lineBreak` for the trailing one. `t` is arbitrary: the claim is about the layout around a
character rather than about which character it is.
-/
private theorem token_before (t : Char) (st : Style) (d : Nat) (x : List Char) :
    Spec.Token t (t :: ((st.lineBreak d).toList ++ x)) x :=
  Spec.Token.mk Spec.Ws.nil (ws_lineBreak st d x)

/--
A line break followed by a closing character is a token in the grammar's sense. A closing bracket
is the one place this layout does write space before a character, so the whitespace falls on the
other side of it.

`Spec.Token t ((st.lineBreak d).toList ++ (t :: x)) x` is built from `ws_lineBreak` for the
leading run and `Ws.nil` for the trailing one, the mirror image of the opening case. `t` is again
arbitrary.
-/
private theorem token_after (t : Char) (st : Style) (d : Nat) (x : List Char) :
    Spec.Token t ((st.lineBreak d).toList ++ (t :: x)) x :=
  Spec.Token.mk (ws_lineBreak st d (t :: x)) Spec.Ws.nil

/--
What the layout writes for a name separator is a `name-separator` token. The compact style writes
a bare colon and the indented style a colon and a space, so the two differ in their trailing
whitespace and have to be treated separately.

`Spec.NameSeparator (st.colon.toList ++ x) x` consumes the separator and leaves `x`. Both branches
take `Ws.nil` for the leading run, no space ever preceding the colon; the compact branch takes
`Ws.nil` after it as well, and the indented branch a single-space run.
-/
private theorem token_colon (st : Style) (x : List Char) :
    Spec.NameSeparator (st.colon.toList ++ x) x := by
  unfold Style.colon
  split
  · simpa using Spec.Token.mk (t := ':') Spec.Ws.nil Spec.Ws.nil
  · exact Spec.Token.mk (s' := ' ' :: x) (by simpa using Spec.Ws.nil (r := ':' :: ' ' :: x))
      (Spec.Ws.cons (by decide) Spec.Ws.nil)

/--
What the layout writes between two items is a `value-separator` token. The comma is followed by a
break in the indented style and by nothing in the compact one, which is the same shape as an
opening bracket.

`Spec.ValueSeparator ((st.precedes d false).toList ++ x) x` consumes the separator and leaves `x`.
`precedes` at `false` is a comma followed by the line break, so this is `token_before` at `','`;
the flag is `false` because at `true` nothing is written, which is what `toList_precedes_true`
records for the first item of a container.
-/
private theorem token_separator (st : Style) (d : Nat) (x : List Char) :
    Spec.ValueSeparator ((st.precedes d false).toList ++ x) x := by
  simpa [Style.precedes, String.toList_append] using token_before ',' st d x

/--
The printer's stack machine emits exactly the characters the recursive description gives. The
machine relates its output to the value only through a loop invariant, so the grammar theorems are
stated about the description instead, and this is the bridge between the two.

`(render st items acc).toList = acc.toList ++ itemsChars st items` says the accumulator is left
alone and the items' characters appended in order. `itemsChars` maps each pending item to its
characters, so the equation is about every intermediate stack rather than only the initial one,
which is what makes it provable by following `render`'s own recursion.
-/
private theorem toList_render (st : Style) (items : List Item) (acc : String) :
    (render st items acc).toList = acc.toList ++ itemsChars st items := by
  fun_induction render st items acc <;>
    simp_all [itemsChars, itemChars, chars, elemChars, memberChars, toList_stringTo]

/-! ## Well-formedness -/

/--
Nothing precedes the first item of a container. The separator logic is one function taking a flag,
and this is the branch that lets the item after an opening bracket begin immediately.

`(st.precedes d true).toList = []` holds in both styles and at every depth. It is what lets
`elemChars` and `memberChars` be started with `true` and still match a derivation that begins with
a value or a member.
-/
private theorem toList_precedes_true (st : Style) (d : Nat) : (st.precedes d true).toList = [] := by
  simp [Style.precedes]

mutual

/--
What the printer writes for a value is a `value` in the grammar's sense, denoting that value. This
is the module's main claim; the two exported theorems are it composed with the description of what
the machine actually emits.

`canonicalNumbers j = true` is required and cannot be dropped: `spec_num` records a number's
normal form, so for a non-canonical number the grammar would derive a different value from the
same text. `Spec.Value (chars st d j ++ r) j r` consumes the rendering and leaves an arbitrary
`r`, which is what lets the claim be used inside a larger derivation. `st` and `d` are arbitrary,
so both styles at every depth are covered at once. The seven alternatives follow the constructors,
with arrays and objects splitting further on whether the container is empty.
-/
private theorem spec_value (st : Style) (d : Nat) : ∀ (j : Json), canonicalNumbers j = true →
    ∀ r, Spec.Value (chars st d j ++ r) j r
  | .null, _, r => by simpa [chars] using Spec.Value.null (r := r)
  | .bool true, _, r => by simpa [chars] using Spec.Value.true_ (r := r)
  | .bool false, _, r => by simpa [chars] using Spec.Value.false_ (r := r)
  | .num n, h, r => by
    have hc : n.Canonical := of_decide_eq_true (by simpa [canonicalNumbers] using h)
    exact Spec.Value.num (by simpa [chars, Number.normalize_eq_self hc] using spec_num n r)
  | .str s, _, r => by exact Spec.Value.str (by simpa [chars] using spec_str s r)
  | .arr elems, h, r => by
    by_cases he : elems.isEmpty
    · obtain rfl : _ = #[] := Array.empty_of_isEmpty he
      refine Spec.Value.arr (Spec.Arr.empty (s' := ']' :: r) ?_ ?_)
      · simpa [chars] using Spec.Token.mk (t := '[') Spec.Ws.nil Spec.Ws.nil
      · simpa using Spec.Token.mk (t := ']') Spec.Ws.nil Spec.Ws.nil
    · have hne : elems.toList ≠ [] := by
        intro h0
        rw [Array.toList_inj.mp (show elems.toList = (#[] : Array Json).toList by simp [h0])] at he
        simp at he
      have harr := Spec.Arr.items (vs := elems.toList)
        (token_before '[' st (d + 1)
          (elemChars st (d + 1) elems.toList true ++ ((st.lineBreak d).toList ++ (']' :: r))))
        (spec_elements st (d + 1) elems.toList (by simpa [canonicalNumbers] using h) hne
          ((st.lineBreak d).toList ++ (']' :: r)))
        (token_after ']' st d r)
      rw [Array.toArray_toList] at harr
      refine Spec.Value.arr ?_
      have hchars : chars st d (.arr elems) =
          ("[" ++ st.lineBreak (d + 1)).toList ++ elemChars st (d + 1) elems.toList true ++
            (st.lineBreak d ++ "]").toList := by
        rw [chars, ite_eq_right he]
      rw [hchars]
      simpa [String.toList_append, List.append_assoc] using harr
  | .obj fields, h, r => by
    by_cases he : fields.isEmpty
    · obtain rfl : _ = #[] := Array.empty_of_isEmpty he
      refine Spec.Value.obj (Spec.Object.empty (s' := '}' :: r) ?_ ?_)
      · simpa [chars] using Spec.Token.mk (t := '{') Spec.Ws.nil Spec.Ws.nil
      · simpa using Spec.Token.mk (t := '}') Spec.Ws.nil Spec.Ws.nil
    · have hne : fields.toList ≠ [] := by
        intro h0
        rw [Array.toList_inj.mp
          (show fields.toList = (#[] : Array (String × Json)).toList by simp [h0])] at he
        simp at he
      have hobj := Spec.Object.members (ms := fields.toList)
        (token_before '{' st (d + 1)
          (memberChars st (d + 1) fields.toList true ++ ((st.lineBreak d).toList ++ ('}' :: r))))
        (spec_members st (d + 1) fields.toList (by simpa [canonicalNumbers] using h) hne
          ((st.lineBreak d).toList ++ ('}' :: r)))
        (token_after '}' st d r)
      rw [Array.toArray_toList] at hobj
      refine Spec.Value.obj ?_
      have hchars : chars st d (.obj fields) =
          ("{" ++ st.lineBreak (d + 1)).toList ++ memberChars st (d + 1) fields.toList true ++
            (st.lineBreak d ++ "}").toList := by
        rw [chars, ite_eq_right he]
      rw [hchars]
      simpa [String.toList_append, List.append_assoc] using hobj

/--
What the printer writes for a non-empty list of values is an array's contents in the grammar's
sense. It is the array half of the mutual induction with the value case, and the separator logic
is where its work lies.

`canonicalNumbersList l = true` requires every element's numbers to be canonical, and `l ≠ []`
is required because `Elements` has no empty derivation, an empty array being handled by
`Arr.empty` instead. The conclusion consumes `elemChars st d l true` and leaves an arbitrary `r`.
The one-element case removes the leading separator with `toList_precedes_true`; the recursive case
takes `precedes` at `false`, which `token_separator` derives.
-/
private theorem spec_elements (st : Style) (d : Nat) :
    ∀ (l : List Json), canonicalNumbersList l = true →
    l ≠ [] → ∀ r, Spec.Elements (elemChars st d l true ++ r) l r
  | [], _, hne, _ => absurd rfl hne
  | [j], h, _, r => by
    have hj : canonicalNumbers j = true := by simpa [canonicalNumbersList] using h
    simpa [elemChars, toList_precedes_true] using
      Spec.Elements.one (spec_value st d j hj r)
  | j :: j' :: rest, h, _, r => by
    obtain ⟨hj, hrest⟩ : canonicalNumbers j = true ∧ canonicalNumbersList (j' :: rest) = true := by
      simpa [canonicalNumbersList, Bool.and_eq_true] using h
    have hmore := Spec.Elements.more
      (spec_value st d j hj
        ((st.precedes d false).toList ++ (elemChars st d (j' :: rest) true ++ r)))
      (token_separator st d (elemChars st d (j' :: rest) true ++ r))
      (spec_elements st d (j' :: rest) hrest (by simp) r)
    simpa [elemChars, toList_precedes_true, List.append_assoc] using hmore

/--
What the printer writes for a non-empty list of fields is an object's contents in the grammar's
sense. It is the object half of the same mutual induction, and it has in addition to place the
colon between each name and its value.

`canonicalNumbersFields l = true` requires every field value's numbers to be canonical, and
`l ≠ []` again excludes the empty case, which `Object.empty` handles. Each member is assembled
from `spec_str` for the name, `token_colon` for the separator and `spec_value` for the value; the
separator between members is `token_separator`, absent before the first by `toList_precedes_true`.
-/
private theorem spec_members (st : Style) (d : Nat) : ∀ (l : List (String × Json)),
    canonicalNumbersFields l = true → l ≠ [] → ∀ r,
      Spec.Members (memberChars st d l true ++ r) l r
  | [], _, hne, _ => absurd rfl hne
  | [(k, v)], h, _, r => by
    have hv : canonicalNumbers v = true := by simpa [canonicalNumbersFields] using h
    have hmem := Spec.Member.mk (spec_str k (st.colon.toList ++ (chars st d v ++ r)))
      (token_colon st (chars st d v ++ r)) (spec_value st d v hv r)
    simpa [memberChars, toList_precedes_true, List.append_assoc] using
      Spec.Members.one hmem
  | (k, v) :: kv' :: rest, h, _, r => by
    obtain ⟨hv, hrest⟩ :
        canonicalNumbers v = true ∧ canonicalNumbersFields (kv' :: rest) = true := by
      simpa [canonicalNumbersFields, Bool.and_eq_true] using h
    have hmem := Spec.Member.mk
      (spec_str k (st.colon.toList ++ (chars st d v ++ ((st.precedes d false).toList ++
        (memberChars st d (kv' :: rest) true ++ r)))))
      (token_colon st (chars st d v ++ ((st.precedes d false).toList ++
        (memberChars st d (kv' :: rest) true ++ r))))
      (spec_value st d v hv ((st.precedes d false).toList ++
        (memberChars st d (kv' :: rest) true ++ r)))
    have hmore := Spec.Members.more hmem
      (token_separator st d (memberChars st d (kv' :: rest) true ++ r))
      (spec_members st d (kv' :: rest) hrest (by simp) r)
    simpa [memberChars, toList_precedes_true, List.append_assoc] using hmore

end

/-! ## What the printer emits is JSON text -/

/--
The compact printer's output is the compact description. It is the machine's initial call resolved
into the recursive form, which is what the exported theorem needs before the grammar claims apply.

`(compress j).toList = chars Style.compact 0 j`. `compress` starts `render` at depth zero with a
single `.val` item and an empty accumulator, so `toList_render` reduces it to `itemsChars` of that
one-item stack, which is `chars` at the same style and depth.
-/
private theorem toList_compress (j : Json) : (compress j).toList = chars Style.compact 0 j := by
  simp [compress, toList_render, itemsChars, itemChars]

/--
The indented printer's output is the indented description, at any indent width. The two printers
differ only in the style they pass, and both have to be reduced to the description before the
grammar claims can be applied.

`(pretty j indent).toList = chars (Style.pretty indent) 0 j`. As in the compact case, `pretty`
starts `render` at depth zero with one `.val` item and an empty accumulator. `indent` is carried
inside the style and is otherwise unconstrained, so every width including zero is covered.
-/
private theorem toList_pretty (j : Json) (indent : Nat) :
    (pretty j indent).toList = chars (Style.pretty indent) 0 j := by
  simp [pretty, toList_render, itemsChars, itemChars]

/--
The description of a value, on its own, is a complete JSON text denoting it. `Text` demands
whitespace, a value and whitespace with nothing left over, so this is where the printer's output
is shown to be a whole document rather than a fragment of one.

`h : CanonicalNumbers j` is inherited from `spec_value`. The witness takes `chars st 0 j` as the
whole text with an empty remainder: both `Ws` runs are `Ws.nil`, the printer writing no leading or
trailing space in either style, and the middle is `spec_value` at the empty remainder. `st` is
arbitrary, so one proof serves both printers.
-/
private theorem spec_text (st : Style) {j : Json} (h : CanonicalNumbers j) :
    Spec.Text (chars st 0 j) j :=
  ⟨chars st 0 j, [], Spec.Ws.nil, by simpa using spec_value st 0 j h [], Spec.Ws.nil⟩

/--
The compressed form of a value is JSON text denoting that value. It is half of what a caller needs
from the printer, and it is the half the round trip composes with the parser's completeness.

`h : CanonicalNumbers j` is required, and it is not an idle condition: a value straight from the
parser satisfies it by `Json.Spec.canonicalNumbers_of_text`, while one a caller built with a
non-canonical number is genuinely excluded. `Spec.TextOf (compress j) j` says the string's
characters form a complete text denoting `j`. It is `toList_compress` followed by `spec_text`.
-/
theorem textOf_compress {j : Json} (h : CanonicalNumbers j) : Spec.TextOf (compress j) j := by
  rw [Spec.TextOf, toList_compress]
  exact spec_text Style.compact h

/--
The laid-out form is JSON text denoting the same value, so the space the printer adds is never
significant. It is proved separately from the compact case because `pretty` is a different
function, not because the argument differs.

`h : CanonicalNumbers j` is required for the same reason as in the compact case, the printer
reproducing only a canonical number faithfully. `indent` is quantified over, so no particular
width is relied on, zero included. It is `toList_pretty` followed by `spec_text` at the indented
style.
-/
theorem textOf_pretty {j : Json} (h : CanonicalNumbers j) (indent : Nat) :
    Spec.TextOf (pretty j indent) j := by
  rw [Spec.TextOf, toList_pretty]
  exact spec_text (Style.pretty indent) h

/--
A rendered string is a string literal denoting the string it came from, whatever it holds. It is
exported on its own because a caller may render a string outside any document, to build a fragment
by hand, and needs to know that what they get back is well formed.

`Spec.Str ((renderString s).toList ++ r) s r` consumes the literal and leaves an arbitrary `r`,
which is what allows the fragment to be embedded in a larger text. `renderString` is
`Printer.string`, so this is `spec_str` restated at the exported name. No condition on `s`
appears, the escaping having dealt with every character.
-/
theorem spec_renderString (s : String) (r : List Char) :
    Spec.Str ((renderString s).toList ++ r) s r := spec_str s r

/--
Anything the printer emits is valid UTF-8, and so meets RFC 8259 section 8.1. The claim is really
about the type rather than about the printer: output is a `String`, and a `String`'s bytes are by
definition the UTF-8 encoding of its characters.

`s.toByteArray.IsValidUTF8` says the bytes decode. `String.utf8Encode_toList` identifies
`toByteArray` with encoding the character list, and `ByteArray.isValidUTF8_utf8Encode` says such
an encoding is valid. Nothing about `s` is used, so it holds of every string; what it establishes
about the printer is that no separate check on its output is needed.
-/
theorem isValidUTF8_toByteArray (s : String) : s.toByteArray.IsValidUTF8 :=
  String.utf8Encode_toList ▸ ByteArray.isValidUTF8_utf8Encode
end Json.Printer
