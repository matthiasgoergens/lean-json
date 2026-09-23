/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Basic

public section

namespace Json.Printer

@[expose] section

/-!
Writing a value out as text.

`compress` and `pretty` share one traversal over an explicit stack of items, so nesting costs
heap rather than C stack, and the text accumulates in a `String`, which makes the validity of
its UTF-8 a property of the type rather than something to maintain by hand.

A number is written out in full while its padding stays short and in exponent notation
otherwise, so `⟨1,2⟩` is `100` and `⟨1,1000000000⟩` is `1e1000000000`. Both read back as the
number they came from.
-/

/-! ## Digits -/

def digitChar (d : Nat) : Char := Char.ofNat ('0'.toNat + d)

def hexDigitChar (d : Nat) : Char :=
  if d < 10 then digitChar d else Char.ofNat ('a'.toNat + (d - 10))

/-- The decimal digits of `n` in front of `acc`, most significant first. -/
def digitCharsTo (n : Nat) (acc : List Char) : List Char :=
  if n < 10 then digitChar n :: acc
  else digitCharsTo (n / 10) (digitChar (n % 10) :: acc)
termination_by n
decreasing_by omega

def digitChars (n : Nat) : List Char := digitCharsTo n []

/-!
Dividing a number by ten to take off its last digit costs a pass over the whole number, so
writing one out a digit at a time is quadratic in its digits. Splitting it in half instead, by
dividing by a power of ten near the middle, keeps both sides of each division the same size,
which is what arbitrary-precision division is fast at. The loop above is the one the grammar
theorems are stated against, and the two are proved equal, so what runs is the halving one.
-/

/-- The last `w` decimal digits of `n`, most significant first, leading zeros included. -/
private def padDigits (n : Nat) : Nat → List Char
  | 0 => []
  | w + 1 => padDigits (n / 10) w ++ [digitChar (n % 10)]

/--
A fixed-width block of digits can be cut anywhere: the high part comes from the number with the
low digits divided away, and the low part from the number itself. The halving renderer splits in
exactly this way, so nothing can be said about it until the split is available.

`padDigits n w` is the last `w` decimal digits of `n`, most significant first and leading zeros
kept. The equation divides a width of `a + b` into a high block of width `a`, taken from
`n / 10 ^ b`, and a low block of width `b`, taken from `n` itself. Taking the low block from `n`
rather than from `n % 10 ^ b` costs nothing, `padDigits` keeping only the last `b` digits anyway.
-/
private theorem padDigits_split (n a : Nat) :
    ∀ b, padDigits n (a + b) = padDigits (n / 10 ^ b) a ++ padDigits n b := by
  intro b
  induction b generalizing n with
  | zero => simp [padDigits]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega, padDigits, ih (n / 10),
      Nat.div_div_eq_div_mul, Nat.mul_comm 10 (10 ^ b), ← Nat.pow_succ, padDigits,
      List.append_assoc]

/--
A fixed-width rendering depends only on the digits it is going to show. The halving renderer
passes its low half a number whose high digits have been removed, and its high half one whose have
not, so the two branches can only be compared once the invisible digits are known not to matter.

`h : n₁ % 10 ^ w = n₂ % 10 ^ w` says the two numbers agree on their last `w` digits. The
conclusion says they render identically at width `w`. The induction is on `w`, splitting each
number into its last digit and the rest, so what is really shown is that the agreement descends.
-/
private theorem padDigits_congr : ∀ (w n₁ n₂ : Nat), n₁ % 10 ^ w = n₂ % 10 ^ w →
    padDigits n₁ w = padDigits n₂ w := by
  intro w
  induction w with
  | zero => intro n₁ n₂ _; simp [padDigits]
  | succ w ih =>
    intro n₁ n₂ h
    rw [show (10 : Nat) ^ (w + 1) = 10 * 10 ^ w by rw [Nat.pow_succ]; omega] at h
    have hlow : n₁ % 10 = n₂ % 10 := by
      rw [← Nat.mod_mul_right_mod n₁ 10 (10 ^ w), ← Nat.mod_mul_right_mod n₂ 10 (10 ^ w), h]
    have hhigh : n₁ / 10 % 10 ^ w = n₂ / 10 % 10 ^ w := by
      rw [← Nat.mod_mul_right_div_self n₁ 10 (10 ^ w), ← Nat.mod_mul_right_div_self n₂ 10 (10 ^ w),
        h]
    rw [padDigits, padDigits, ih _ _ hhigh, hlow]

/--
Zero at a fixed width is that many zero characters. The renderer pads to a generous width and
strips the leading zeros afterwards, so exactly what a zero high part contributes has to be known
before the strip can be described.

`padDigits 0 w = List.replicate w '0'` is an equation between lists of characters, so it says the
padding is literally `'0'` repeated and nothing besides. It holds at every width, including zero,
where both sides are empty.
-/
private theorem padDigits_zero (w : Nat) : padDigits 0 w = List.replicate w '0' := by
  induction w with
  | zero => simp [padDigits]
  | succ w ih => simp [padDigits, ih, List.replicate_succ', digitChar]

/-- The last `w` digits of `n` in front of `acc`, by halving rather than a digit at a time. -/
def renderExact (n : Nat) : Nat → List Char → List Char
  | 0, acc => acc
  | 1, acc => digitChar (n % 10) :: acc
  | w + 2, acc =>
    let h := (w + 2) / 2
    renderExact (n / 10 ^ h) (w + 2 - h) (renderExact (n % 10 ^ h) h acc)
termination_by w => w
decreasing_by
  · omega
  · omega

/--
The halving renderer writes exactly the fixed-width block of digits, in front of what has already
been accumulated. Taking digits off one at a time costs a pass over the whole number each time, so
writing a long one out is quadratic in its digits; halving keeps both sides of every division the
same length, which is what arbitrary-precision division is fast at, and this is what says the fast
form still writes the right characters.

`renderExact n w acc` halves the width and renders the two parts; `padDigits n w ++ acc` is the
block prepended to the accumulator. Stating it for an arbitrary `acc` is what makes it an
induction hypothesis. That induction follows `renderExact`'s own recursion, with `padDigits_split`
cutting the block in two and `padDigits_congr` saying the low half may be rendered from
`n % 10 ^ h` or from `n` indifferently.
-/
private theorem renderExact_eq (n w : Nat) (acc : List Char) :
    renderExact n w acc = padDigits n w ++ acc := by
  fun_induction renderExact n w acc with
  | case1 => simp [padDigits]
  | case2 n acc => simp [padDigits]
  | case3 n w acc h _ ihLow ihHigh =>
    rw [ihHigh, ihLow, padDigits_congr h (n % 10 ^ h) n (by simp [Nat.mod_mod_of_dvd]),
      ← List.append_assoc, ← padDigits_split n (w + 2 - h) h]
    congr 2
    omega

/--
Stripping leading zeros passes straight over a block of zeros. The renderer pads to a width that
is usually wider than the number, so its output ordinarily begins with a run of zeros, and that
run has to be shown to leave nothing behind.

`dropWhile (· == '0')` removes leading zero characters. The equation says a prefix of `w` of them
contributes nothing to the result, whatever `Y` is, including a `Y` that itself begins with zeros,
where the strip simply carries on. The induction is on `w`.
-/
private theorem dropWhile_replicate_append (w : Nat) (Y : List Char) :
    (List.replicate w '0' ++ Y).dropWhile (· == '0') = Y.dropWhile (· == '0') := by
  induction w with
  | zero => simp
  | succ w ih => simp [List.replicate_succ, ih]

/--
Stripping a prefix halts inside the first part whenever that part does not vanish entirely, and
the second part is then left alone. This is the other half of describing the strip: a non-zero
number's leading digit stops the scan, and everything after it is carried along unexamined.

`h : X.dropWhile p ≠ []` says stripping `X` on its own leaves something, so the scan halts
within `X`. The conclusion `(X ++ Y).dropWhile p = X.dropWhile p ++ Y` says `Y` is neither
examined nor altered. The hypothesis cannot be dropped: an `X` that strips away entirely lets the
scan run on into `Y`.
-/
private theorem dropWhile_append_of_ne_nil {p : Char → Bool} {X Y : List Char}
    (h : X.dropWhile p ≠ []) : (X ++ Y).dropWhile p = X.dropWhile p ++ Y := by
  induction X with
  | nil => simp at h
  | cons c t ih =>
    simp only [List.cons_append, List.dropWhile_cons] at h ⊢
    split
    · exact ih (by simpa [*] using h)
    · rfl

/--
A non-zero digit is not written as the character `'0'`. Stripping leading zeros is stated over
characters while the digits being stripped are numbers, and this is what makes the strip stop at
the first significant digit rather than run past it.

`h : d ≠ 0` and `h' : d < 10` between them confine `d` to nine values, which the proof checks
one by one; the upper bound is what makes that case analysis finite, and without it `digitChar`
would be applied outside the digits it is defined for. The conclusion is that `digitChar d`
differs from `'0'`.
-/
private theorem digitChar_ne_zero {d : Nat} (h : d ≠ 0) (h' : d < 10) : digitChar d ≠ '0' := by
  have : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/--
The accumulating digit renderer prepends a number's digits to whatever it was given. `digitChars`
is this function started on the empty accumulator, so nothing about a part-built rendering can be
said until the accumulator is known to be carried along untouched.

`digitCharsTo n acc` builds the digits in front of `acc`, and `digitChars n ++ acc` is the digits
followed by `acc`. The equation holds for every accumulator, which is what makes it usable as an
induction hypothesis; the induction is strong recursion on `n`, following the division by ten.
-/
private theorem digitCharsTo_nil (n : Nat) : ∀ acc, digitCharsTo n acc = digitChars n ++ acc := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro acc
    rw [digitChars]
    by_cases hn : n < 10
    · rw [digitCharsTo, ite_eq_left hn, digitCharsTo, ite_eq_left hn]
      simp
    · rw [digitCharsTo, ite_eq_right hn, ih (n / 10) (by omega) (digitChar (n % 10) :: acc),
        digitCharsTo, ite_eq_right hn, ih (n / 10) (by omega) [digitChar (n % 10)]]
      simp

/--
A number of more than one digit is written as its leading digits followed by its last. This is the
recursion `digitCharsTo` performs, restated on the accumulator-free form that the claims about
stripping zeros are proved against.

`h : ¬ n < 10` selects the recursive branch, and is needed: at `n < 10` the right-hand side would
prefix a spurious `digitChars 0`, namely `'0'`, to a single digit. The conclusion peels
`digitChar (n % 10)` off the end and leaves `digitChars (n / 10)` in front, and follows from
`digitCharsTo_nil` with the accumulator holding that last digit.
-/
private theorem digitChars_cons (n : Nat) (h : ¬ n < 10) :
    digitChars n = digitChars (n / 10) ++ [digitChar (n % 10)] := by
  rw [digitChars, digitCharsTo, ite_eq_right h, digitCharsTo_nil]

/--
Every number renders as at least one character. Stripping leading zeros has to leave something
behind for a non-zero number, and this is where that something comes from.

`digitChars n ≠ []` holds for every natural number, zero included, which renders as the single
character `'0'`. The two cases follow the definition: below ten a one-character list, and at ten
or above a list ending in the last digit, neither of which can be empty.
-/
private theorem digitChars_ne_nil (n : Nat) : digitChars n ≠ [] := by
  by_cases hn : n < 10
  · rw [digitChars, digitCharsTo, ite_eq_left hn]; simp
  · rw [digitChars_cons n hn]; simp

/--
Stripping the leading zeros from a fixed-width rendering leaves exactly the number's ordinary
digits. This is the claim that joins the fast renderer to the one every grammar theorem is stated
against: pad to a generous width, strip, and what remains is the spelling `digitChars` gives.

`n ≠ 0` is required because zero would strip away to nothing rather than to `['0']`, which is
why `digitCharsFast` handles it separately. `n < 10 ^ w` says the width is wide enough to hold the
number, so the strip can only remove padding and never a significant digit. The induction is on
`w`: once `n` has fallen below ten, `padDigits_zero` and `dropWhile_replicate_append` clear the
padding, and above that `dropWhile_append_of_ne_nil` with `digitChars_ne_nil` says the strip halts
in the high digits.
-/
private theorem dropWhile_padDigits : ∀ (w n : Nat), n ≠ 0 → n < 10 ^ w →
    (padDigits n w).dropWhile (· == '0') = digitChars n := by
  intro w
  induction w with
  | zero => intro n hn h; simp at h; omega
  | succ w ih =>
    intro n hn h
    have hlt : n / 10 < 10 ^ w := by
      rw [Nat.div_lt_iff_lt_mul (by omega), ← Nat.pow_succ]
      exact h
    rw [padDigits]
    by_cases h10 : n < 10
    · rw [show n / 10 = 0 by omega, padDigits_zero, dropWhile_replicate_append,
        show n % 10 = n by omega, digitChars, digitCharsTo, ite_eq_left h10]
      simp [digitChar_ne_zero hn h10]
    · have hne : n / 10 ≠ 0 := by omega
      rw [dropWhile_append_of_ne_nil (by rw [ih (n / 10) hne hlt]; exact digitChars_ne_nil _),
        ih (n / 10) hne hlt, ← digitChars_cons n h10]

/-- A power of two at least as large as the number of digits, found by squaring. -/
def widthBound (n : Nat) : Nat := go 1 10 (by omega)
where
  go (w p : Nat) (hp : 2 ≤ p) : Nat :=
    if n < p then w
    else go (2 * w) (p * p) (by have := Nat.mul_le_mul_left p hp; omega)
  termination_by n + 1 - p
  decreasing_by
    have := Nat.mul_le_mul_left p hp
    omega

/--
The width search halts at a power of two wide enough to hold the number, and never at zero.
Squaring the candidate rather than incrementing it is what keeps finding a width logarithmic in
the digits, and this says the width it lands on is still wide enough to render into.

`hp : 2 ≤ p`, `p = 10 ^ w` and `1 ≤ w` are the invariant the loop maintains: the candidate
width and the power it is being tested against move together, and the width stays positive. The
conclusion gives both halves of what the caller needs, `n < 10 ^ (result)`, so the width holds
`n`, and `1 ≤ result`, so the width is never zero. The induction follows the loop, where each
step squares `p` and doubles `w`, which is why the invariant is stated as an equation rather than
an inequality.
-/
private theorem widthBound_go_spec (n : Nat) : ∀ (w p : Nat) (hp : 2 ≤ p), p = 10 ^ w → 1 ≤ w →
    n < 10 ^ (widthBound.go n w p hp) ∧ 1 ≤ widthBound.go n w p hp := by
  intro w p hp
  fun_induction widthBound.go n w p hp with
  | case1 w p hp h => intro hpw hw; exact ⟨hpw ▸ h, hw⟩
  | case2 w p hp h ih =>
    intro hpw hw
    exact ih (by rw [hpw, ← Nat.pow_add]; congr 1; omega) (by omega)

/--
The width the search returns is wide enough to hold the number. This is all the fast renderer asks
of it: too wide costs a few zeros that the strip removes anyway, while too narrow would lose the
leading digits outright.

`n < 10 ^ widthBound n` holds for every natural number, with no hypothesis. It is
`widthBound_go_spec` at the loop's starting point, `w = 1` and `p = 10`, where the invariant
`p = 10 ^ w` is `Nat.pow_one` and the positivity of `w` is immediate.
-/
private theorem widthBound_spec (n : Nat) : n < 10 ^ widthBound n :=
  (widthBound_go_spec n 1 10 (by omega) (Nat.pow_one 10).symm (by omega)).1

def digitCharsFast (n : Nat) : List Char :=
  if n = 0 then ['0'] else (renderExact n (widthBound n) []).dropWhile (· == '0')

/--
The compiler writes digits by halving rather than one at a time. Every claim tying the printer to
the grammar is about `digitChars`, and what runs is `digitCharsFast`; this is what makes them one
program, and it is why writing a thousand-digit number does not cost time quadratic in its digits.

`@digitChars = @digitCharsFast` is an equation between the functions, over every natural number,
which is what `@[csimp]` requires before it will substitute one for the other in compiled code.
`digitCharsFast` answers `['0']` at zero, and otherwise renders at `widthBound n` and strips the
leading zeros, which `renderExact_eq`, `widthBound_spec` and `dropWhile_padDigits` together
identify with `digitChars n`.
-/
@[csimp] theorem digitChars_eq_digitCharsFast : @digitChars = @digitCharsFast := by
  funext n
  rw [digitCharsFast]
  split
  · next h => rw [h, digitChars, digitCharsTo, ite_eq_left (by omega)]; rfl
  · next h => rw [renderExact_eq, List.append_nil, dropWhile_padDigits _ n h (widthBound_spec n)]

def digitString (n : Nat) : String := String.ofList (digitChars n)

def zeros (n : Nat) : String := String.ofList (List.replicate n '0')

def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-! ## Numbers -/

/-- Padding longer than this is written as an exponent instead. -/
def plainZeroLimit : Nat := 20

/--
A number as JSON text: plain decimal notation while that costs at most `plainZeroLimit`
characters of padding, and exponent notation beyond it, so `⟨1, 2⟩` is `100` while
`⟨1, 1000000000⟩` is `1e1000000000`. Both spellings denote the same value, so round tripping
is unaffected by which one is chosen.
-/
def number (n : Number) : String :=
  if n.mantissa = 0 then
    "0"
  else
    let sign := if n.mantissa < 0 then "-" else ""
    let ds := digitChars n.mantissa.natAbs
    let mantissa := String.ofList ds
    let exponentForm :=
      if n.exponent < 0 then mantissa ++ "e-" ++ digitString (-n.exponent).toNat
      else mantissa ++ "e" ++ digitString n.exponent.toNat
    if n.exponent = 0 then
      sign ++ mantissa
    else if 0 < n.exponent then
      if n.exponent ≤ (plainZeroLimit : Int) then sign ++ mantissa ++ zeros n.exponent.toNat
      else sign ++ exponentForm
    else
      let k := (-n.exponent).toNat
      if k < ds.length then
        sign ++ String.ofList (ds.take (ds.length - k)) ++ "." ++
          String.ofList (ds.drop (ds.length - k))
      else if k - ds.length ≤ plainZeroLimit then
        sign ++ "0." ++ zeros (k - ds.length) ++ mantissa
      else
        sign ++ exponentForm

/-! ## Strings -/

/--
`c` as it appears inside a string literal: the two escapes RFC 8259 requires, the short forms
for the control characters that have one, and `\uXXXX` for the remaining controls. Everything
else stands for itself, the output being UTF-8.
-/
def escapeChars (c : Char) : List Char :=
  match c with
  | '"' => ['\\', '"']
  | '\\' => ['\\', '\\']
  | '\x08' => ['\\', 'b']
  | '\x0c' => ['\\', 'f']
  | '\n' => ['\\', 'n']
  | '\x0d' => ['\\', 'r']
  | '\t' => ['\\', 't']
  | c =>
    if c.toNat < 0x20 then
      ['\\', 'u', '0', '0', hexDigitChar (c.toNat / 16), hexDigitChar (c.toNat % 16)]
    else
      [c]

def escapeCharTo (acc : String) (c : Char) : String :=
  match c with
  | '"' => acc ++ "\\\""
  | '\\' => acc ++ "\\\\"
  | '\x08' => acc ++ "\\b"
  | '\x0c' => acc ++ "\\f"
  | '\n' => acc ++ "\\n"
  | '\x0d' => acc ++ "\\r"
  | '\t' => acc ++ "\\t"
  | c =>
    if c.toNat < 0x20 then
      ((acc ++ "\\u00").push (hexDigitChar (c.toNat / 16))).push (hexDigitChar (c.toNat % 16))
    else
      acc.push c

def escapeTo (acc : String) (s : String) : String := s.foldl escapeCharTo acc

/-- `s` as a string literal, quotation marks included, appended to `acc`. -/
def stringTo (acc : String) (s : String) : String := (escapeTo (acc.push '"') s).push '"'

def string (s : String) : String := stringTo "" s

/-! ## Layout -/

/-- How a value is laid out: `none` for the compact form, `some k` to indent each level by `k`. -/
structure Style where
  indent : Option Nat
deriving Inhabited

def Style.compact : Style := ⟨none⟩

def Style.pretty (indent : Nat := 2) : Style := ⟨some indent⟩

/-- The break and indentation that precede an item at `depth`, empty in the compact form. -/
def Style.lineBreak (st : Style) (depth : Nat) : String :=
  match st.indent with
  | none => ""
  | some k => "\n" ++ spaces (k * depth)

def Style.colon (st : Style) : String :=
  match st.indent with
  | none => ":"
  | some _ => ": "

/-! ## The traversal -/

/--
One step of pending output: text already decided, a value still to render, or the elements or
members of a container that has been entered. `first` distinguishes the item that follows the
opening bracket from those that need a separator in front of them.
-/
inductive Item where
  | lit (s : String)
  | val (depth : Nat) (j : Json)
  | elems (depth : Nat) (rest : List Json) (first : Bool)
  | members (depth : Nat) (rest : List (String × Json)) (first : Bool)

-- The measure the traversal decreases. Only the shape counts: each element or member allows for
-- the separator that may precede it, and each container for its two brackets.
mutual

def size : Json → Nat
  | .null => 1
  | .bool _ => 1
  | .num _ => 1
  | .str _ => 1
  | .arr elems => 2 + sizeList elems.toList
  | .obj fields => 2 + sizeFields fields.toList

def sizeList : List Json → Nat
  | [] => 1
  | j :: rest => size j + 1 + sizeList rest

def sizeFields : List (String × Json) → Nat
  | [] => 1
  | (_, v) :: rest => size v + 1 + sizeFields rest

end

def Item.weight : Item → Nat
  | .lit _ => 1
  | .val _ j => 2 * size j
  | .elems _ l _ => 2 * sizeList l
  | .members _ l _ => 2 * sizeFields l

def weight : List Item → Nat
  | [] => 0
  | i :: rest => i.weight + weight rest

/-- The text that precedes an element or member: nothing for the first, a separator otherwise. -/
def Style.precedes (st : Style) (depth : Nat) (first : Bool) : String :=
  if first then "" else "," ++ st.lineBreak depth

/--
The traversal itself, over an explicit stack of pending output rather than the call stack, so
that a deeply nested value costs heap and cannot overflow. Every step retires one item and
pushes at most two smaller ones.
-/
def render (st : Style) : List Item → String → String
  | [], acc => acc
  | .lit s :: rest, acc => render st rest (acc ++ s)
  | .val _ .null :: rest, acc => render st rest (acc ++ "null")
  | .val _ (.bool true) :: rest, acc => render st rest (acc ++ "true")
  | .val _ (.bool false) :: rest, acc => render st rest (acc ++ "false")
  | .val _ (.num n) :: rest, acc => render st rest (acc ++ number n)
  | .val _ (.str s) :: rest, acc => render st rest (stringTo acc s)
  | .val d (.arr elems) :: rest, acc =>
    if elems.isEmpty then
      render st rest (acc ++ "[]")
    else
      render st (.elems (d + 1) elems.toList true :: .lit (st.lineBreak d ++ "]") :: rest)
        (acc ++ "[" ++ st.lineBreak (d + 1))
  | .val d (.obj fields) :: rest, acc =>
    if fields.isEmpty then
      render st rest (acc ++ "{}")
    else
      render st (.members (d + 1) fields.toList true :: .lit (st.lineBreak d ++ "}") :: rest)
        (acc ++ "{" ++ st.lineBreak (d + 1))
  | .elems _ [] _ :: rest, acc => render st rest acc
  | .elems d (j :: l) first :: rest, acc =>
    render st (.val d j :: .elems d l false :: rest) (acc ++ st.precedes d first)
  | .members _ [] _ :: rest, acc => render st rest acc
  | .members d ((k, v) :: l) first :: rest, acc =>
    render st (.val d v :: .members d l false :: rest)
      (stringTo (acc ++ st.precedes d first) k ++ st.colon)
termination_by items _ => weight items
decreasing_by all_goals simp only [weight, Item.weight, size, sizeList, sizeFields] <;> omega

end

end Json.Printer

namespace Json

@[expose] section

namespace Number

/-- The canonical spelling of `n` as JSON text. -/
def toString (n : Number) : String := Printer.number n

instance : ToString Number := ⟨toString⟩

end Number

/-- The body of a string literal: `s` escaped as RFC 8259 requires, without quotation marks. -/
def escape (s : String) : String := Printer.escapeTo "" s

/-- `s` as a JSON string literal, quotation marks included. -/
def renderString (s : String) : String := Printer.string s

/-- `j` as JSON text with no space beyond what the grammar requires. -/
def compress (j : Json) : String := Printer.render Printer.Style.compact [.val 0 j] ""

/-- `j` as JSON text laid out over several lines, each level indented by `indent` spaces. -/
def pretty (j : Json) (indent : Nat := 2) : String :=
  Printer.render (Printer.Style.pretty indent) [.val 0 j] ""

instance : ToString Json := ⟨compress⟩

end

end Json
