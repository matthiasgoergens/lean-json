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

/-!
`number` builds its text from lists of characters and several intermediate strings, and finds a
number's digits by halving, which computes powers of ten as arbitrary-precision numbers even for a
number of two digits. What runs instead writes onto the text already accumulated, and takes digits
off one at a time while the number fits a machine word, where a division is cheap.
-/

/-- `acc` followed by the decimal digits of `n`. Quadratic in the digits of a long number. -/
def pushDigits (acc : String) (n : Nat) : String :=
  if n < 10 then acc.push (digitChar n) else (pushDigits acc (n / 10)).push (digitChar (n % 10))
termination_by n
decreasing_by omega

/--
`acc` followed by the last `w` decimal digits of `n`, leading zeros included. Width one is a case
of its own so that the compiler takes `acc` as owned rather than borrowed; borrowed, every push
would copy the whole accumulated text.
-/
def pushPadDigits (acc : String) (n : Nat) : Nat → String
  | 0 => acc
  | 1 => acc.push (digitChar (n % 10))
  | w + 2 => (pushPadDigits acc (n / 10) (w + 1)).push (digitChar (n % 10))

/--
Numbers below this are written a digit at a time; it is `10 ^ 18`, below `2 ^ 63`. Inlined, a
literal this large would be rebuilt from its decimal digits at every use.
-/
@[noinline] def smallBound : Nat := 1000000000000000000

def digitsTo (acc : String) (n : Nat) : String :=
  if n < smallBound then pushDigits acc n else acc ++ digitString n

def digitCount (n : Nat) : Nat :=
  if n < 10 then 1 else digitCount (n / 10) + 1
termination_by n
decreasing_by omega

def pow10 : Nat → Nat
  | 0 => 1
  | k + 1 => pow10 k * 10

/-- `acc ++ number n`, written onto `acc` while the mantissa is below `smallBound`. -/
def numberTo (acc : String) (n : Number) : String :=
  if n.mantissa = 0 then
    acc.push '0'
  else
    let m := n.mantissa.natAbs
    if m < smallBound then
      let acc := if n.mantissa < 0 then acc.push '-' else acc
      if n.exponent = 0 then
        pushDigits acc m
      else if 0 < n.exponent then
        if n.exponent ≤ (plainZeroLimit : Int) then (pushDigits acc m).pushn '0' n.exponent.toNat
        else digitsTo ((pushDigits acc m).push 'e') n.exponent.toNat
      else
        let k := (-n.exponent).toNat
        let len := digitCount m
        if k < len then
          pushPadDigits ((pushDigits acc (m / pow10 k)).push '.') m k
        else if k - len ≤ plainZeroLimit then
          pushDigits ((((acc.push '0').push '.').pushn '0' (k - len))) m
        else
          digitsTo (((pushDigits acc m).push 'e').push '-') k
    else
      acc ++ number n

def numberFast (n : Number) : String := numberTo "" n

/--
Pushing a character `n` times appends `n` copies of it. The fast number writer pads with
`String.pushn`, while `number` pads with `zeros`, a string built from a list.

`s.pushn c n` pushes `c` onto `s` `n` times, and the equation gives its characters as those of
`s` followed by `List.replicate n c`. The induction is on `n`, through `String.pushn`'s definition
as an iterated push.
-/
private theorem toList_pushn (s : String) (c : Char) (n : Nat) :
    (s.pushn c n).toList = s.toList ++ List.replicate n c := by
  rw [String.pushn_eq_repeat_push]
  induction n with
  | zero => simp [Nat.repeat]
  | succ n ih => simp [Nat.repeat, ih, List.replicate_succ']

/--
Writing digits one at a time onto a string appends exactly `digitChars n`. Every claim about the
grammar is stated against `digitChars`, so this is what lets the fast writer stand in for it.

`(pushDigits acc n).toList` is the text the fast writer produces, and the equation says it is
`acc`'s characters followed by `digitChars n`, for every `n`, however long. The induction is
strong recursion on `n`, following the division by ten, with `digitChars_cons` peeling the same
last digit off the right-hand side.
-/
private theorem toList_pushDigits (acc : String) (n : Nat) :
    (pushDigits acc n).toList = acc.toList ++ digitChars n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [pushDigits]
    by_cases h : n < 10
    · rw [ite_eq_left h, digitChars, digitCharsTo, ite_eq_left h]; simp
    · rw [ite_eq_right h, String.toList_push, ih (n / 10) (by omega), digitChars_cons n h]; simp

/--
Writing a fixed width of digits onto a string appends exactly `padDigits n w`. The fast writer
uses it for the digits after a decimal point, which keep their leading zeros.

`(pushPadDigits acc n w).toList` is what the writer produces, and `padDigits n w` is the last `w`
digits of `n`, zeros included. The induction is on `w`, and both sides recurse on `n / 10` in
step.
-/
private theorem toList_pushPadDigits (acc : String) (n w : Nat) :
    (pushPadDigits acc n w).toList = acc.toList ++ padDigits n w := by
  induction w generalizing n with
  | zero => simp [pushPadDigits, padDigits]
  | succ w ih =>
    cases w with
    | zero => simp [pushPadDigits, padDigits]
    | succ w =>
      rw [pushPadDigits, String.toList_push, ih, List.append_assoc]
      conv => rhs; rw [padDigits]

/--
`digitsTo` appends the digits of `n` whichever way it writes them. Small numbers are written a
digit at a time and large ones through `digitString`, which halves, and both give `digitChars n`.

`(digitsTo acc n).toList` is the text produced, and the equation gives it as `acc`'s characters
followed by `digitChars n`, with no condition on `n`: the bound only chooses the method.
-/
private theorem toList_digitsTo (acc : String) (n : Nat) :
    (digitsTo acc n).toList = acc.toList ++ digitChars n := by
  rw [digitsTo]
  split
  · exact toList_pushDigits acc n
  · simp [digitString]

/--
`digitCount` counts the characters `digitChars` produces. The fast writer compares the exponent
with this count, where `number` compares it with the length of the list of digits.

`digitCount n = (digitChars n).length` holds for every `n`, zero included, which has one digit.
The induction is strong recursion on `n`, both sides adding one for each division by ten.
-/
private theorem digitCount_eq (n : Nat) : digitCount n = (digitChars n).length := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [digitCount]
    by_cases h : n < 10
    · rw [ite_eq_left h, digitChars, digitCharsTo, ite_eq_left h]; rfl
    · rw [ite_eq_right h, ih (n / 10) (by omega), digitChars_cons n h]; simp

/--
`pow10` is ten to the power `k`. The fast writer multiplies its way to the power it divides by,
where `Nat.pow` would compute it as an arbitrary-precision number.

`pow10 k = 10 ^ k` for every `k`, by induction on `k`, both sides multiplying by ten at each step.
-/
private theorem pow10_eq (k : Nat) : pow10 k = 10 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow10, ih, Nat.pow_succ]

/--
A fixed-width block of digits has exactly that many characters. Splitting a number's digits at a
decimal point needs the length of the part after it.

`(padDigits n w).length = w` holds for every `n`, the block keeping leading zeros. The induction
is on `w`.
-/
private theorem length_padDigits (n w : Nat) : (padDigits n w).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [padDigits, ih]

/--
A number of at least `k + 1` digits is written as its digits above the last `k`, followed by those
last `k` as a fixed-width block. This is how the fast writer splits a mantissa at a decimal point,
by division rather than by cutting a list.

`h : 10 ^ k ≤ n` says `n` has more than `k` digits, so the high part `n / 10 ^ k` is not zero and
contributes its own digits; without it the high part would be written as a spurious `0`. The
induction is on `k`, peeling one digit off the right of both sides.
-/
private theorem digitChars_split : ∀ (k n : Nat), 10 ^ k ≤ n →
    digitChars n = digitChars (n / 10 ^ k) ++ padDigits n k := by
  intro k
  induction k with
  | zero => intro n _; simp [padDigits]
  | succ k ih =>
    intro n h
    have h10 : ¬ n < 10 := by
      have := Nat.le_self_pow (Nat.succ_ne_zero k) 10
      omega
    have hk : 10 ^ k ≤ n / 10 := by
      rw [Nat.le_div_iff_mul_le (by omega), ← Nat.pow_succ]; exact h
    rw [digitChars_cons n h10, ih (n / 10) hk, padDigits, Nat.div_div_eq_div_mul,
      Nat.mul_comm 10 (10 ^ k), ← Nat.pow_succ, List.append_assoc]

/--
A non-zero number with more than `k` digits is at least `10 ^ k`. This turns the fast writer's
comparison of `k` with the digit count into the bound `digitChars_split` needs.

`hn : n ≠ 0` is needed because zero is written as one digit while being below `10 ^ 0`. `hk` says
`k` is less than the number of digits. The induction is strong recursion on `n`.
-/
private theorem pow_le_of_lt_length : ∀ (n k : Nat), n ≠ 0 → k < (digitChars n).length →
    10 ^ k ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro k hn hk
    by_cases h : n < 10
    · rw [digitChars, digitCharsTo, ite_eq_left h] at hk
      simp at hk
      subst hk
      simp; omega
    · rw [digitChars_cons n h] at hk
      simp at hk
      cases k with
      | zero => simp; omega
      | succ k =>
        have := ih (n / 10) (by omega) k (by omega) (by omega)
        rw [Nat.pow_succ]
        omega

/--
Writing a number onto the accumulated text is appending its spelling. Every claim tying numbers to
the grammar is about `number`, and what runs is `numberTo`; this makes them one program.

`numberTo acc n = acc ++ number n` holds for every accumulator and number. Below `smallBound` the
proof follows `number`'s cases one by one, matching each piece of text through the lemmas above;
from `smallBound` up, `numberTo` is that append by definition.
-/
private theorem numberTo_eq (acc : String) (n : Number) : numberTo acc n = acc ++ number n := by
  rw [numberTo, number]
  by_cases h0 : n.mantissa = 0
  · simp only [h0, ite_true]; rw [← String.toList_inj]; simp
  simp only [h0, ite_false]
  by_cases hs : ¬ n.mantissa.natAbs < smallBound
  · simp [hs]
  simp only [Decidable.not_not] at hs
  simp only [hs, ite_true]
  rw [← String.toList_inj]
  have hsign : (if n.mantissa < 0 then acc.push '-' else acc).toList =
      acc.toList ++ (if n.mantissa < 0 then "-" else "").toList := by
    split <;> simp
  by_cases he : n.exponent = 0
  · simp [he, toList_pushDigits, hsign]
  by_cases hp : 0 < n.exponent
  · by_cases hz : n.exponent ≤ (plainZeroLimit : Int)
    · simp [he, hp, hz, toList_pushDigits, toList_pushn, hsign, zeros]
    · have hn : ¬ n.exponent < 0 := by omega
      simp [he, hp, hz, hn, toList_pushDigits, toList_digitsTo, hsign, digitString]
  · have hn : n.exponent < 0 := by omega
    simp only [he, hp, ite_false, hn, ite_true, ← digitCount_eq]
    by_cases hk : (-n.exponent).toNat < digitCount n.mantissa.natAbs
    · have hle := pow_le_of_lt_length _ _ (by omega) (digitCount_eq _ ▸ hk)
      have hsplit := digitChars_split _ _ hle
      have hlen : digitCount n.mantissa.natAbs - (-n.exponent).toNat =
          (digitChars (n.mantissa.natAbs / 10 ^ (-n.exponent).toNat)).length := by
        rw [digitCount_eq, hsplit, List.length_append, length_padDigits]; omega
      simp only [hk, ite_true, toList_pushPadDigits, String.toList_push, toList_pushDigits,
        pow10_eq, hsign, String.toList_append, String.toList_ofList, hlen]
      rw [hsplit, List.take_left', List.drop_left'] <;> simp
    · by_cases hz : (-n.exponent).toNat - digitCount n.mantissa.natAbs ≤ plainZeroLimit
      · simp [hk, hz, toList_pushDigits, toList_pushn, hsign, zeros]
      · simp [hk, hz, toList_pushDigits, toList_digitsTo, hsign, digitString]

/--
The compiled `number` writes onto an empty string through `numberTo`, so callers of `number`,
`Number.toString` among them, get the fast writer too.

`@number = @numberFast` equates the functions over every number, as `@[csimp]` requires.
`numberFast n` is `numberTo "" n`, which `numberTo_eq` makes `"" ++ number n`.
-/
@[csimp] theorem number_eq_numberFast : @number = @numberFast := by
  funext n
  rw [numberFast, numberTo_eq, String.empty_append]

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

/-! Most characters stand for themselves, so what runs copies each stretch of them in one append
and visits `escapeCharTo` only for the characters that change. -/

def needsEscape (c : Char) : Bool := c.val < 0x20 || c == '"' || c == '\\'

/--
`s` from `p` on escaped onto `acc`, where the characters from `start` up to `p` stand for
themselves and are still to be copied.
-/
def escapeRunTo (s acc : String) (start p : s.Pos) : String :=
  if h : p = s.endPos then
    if start = s.startPos then acc ++ s else acc ++ s.extract start p
  else
    let c := p.get h
    if needsEscape c then
      escapeRunTo s (escapeCharTo (acc ++ s.extract start p) c) (p.next h) (p.next h)
    else escapeRunTo s acc start (p.next h)
termination_by p
decreasing_by all_goals exact String.Pos.lt_next

def escapeToFast (acc s : String) : String := escapeRunTo s acc s.startPos s.startPos

/--
A character that needs no escape is written as itself. This is what lets a stretch of such
characters be copied in one append rather than offered to `escapeCharTo` one at a time.

`h : needsEscape c = false` says `c` is neither a control character, a quotation mark nor a
backslash, which are exactly the characters `escapeCharTo` treats specially; the equation says
that otherwise it pushes `c` onto `acc` unchanged.
-/
private theorem escapeCharTo_of_not_needsEscape {c : Char} (acc : String)
    (h : needsEscape c = false) : escapeCharTo acc c = acc.push c := by
  simp only [needsEscape, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
    decide_eq_false_iff_not] at h
  obtain ⟨⟨hlt, hq⟩, hb⟩ := h
  have hlt' : ¬ c.toNat < 0x20 := by rw [UInt32.lt_iff_toNat_lt] at hlt; exact hlt
  fun_cases escapeCharTo acc c <;> first | rfl | simp_all | exact absurd (by decide) hlt

/--
Copying by stretches writes what escaping one character at a time writes. The invariant carries
the stretch still to be copied, so the claim covers every point of the scan, not only its start.

`start` splits `s` into `t₁` and `r ++ t₂`, and `p` splits it into `t₁ ++ r` and `t₂`: so `r` is
the text between `start` and `p`, waiting to be copied, and `t₂` is what is still to be scanned.
The conclusion says the scan produces `acc` and `r`, followed by `t₂` folded through
`escapeCharTo`, which is `escapeTo`'s own definition.
-/
private theorem escapeRunTo_eq (s acc : String) (start p : s.Pos) :
    ∀ (t₁ r t₂ : String), start.Splits t₁ (r ++ t₂) → p.Splits (t₁ ++ r) t₂ →
    escapeRunTo s acc start p = t₂.toList.foldl escapeCharTo (acc ++ r) := by
  fun_induction escapeRunTo s acc start p with
  | case1 acc =>
    intro t₁ r t₂ h₁ h₂
    obtain rfl : t₂ = "" := h₂.eq_endPos_iff.mp rfl
    obtain rfl : t₁ = "" := h₁.eq_startPos_iff.mp rfl
    have hs : s = r := by simpa using h₁.eq_append
    simp [hs]
  | case2 acc start _ =>
    intro t₁ r t₂ h₁ h₂
    obtain rfl : t₂ = "" := h₂.eq_endPos_iff.mp rfl
    obtain ⟨hle, hr⟩ := String.copy_slice_eq_iff_splits.mpr ⟨t₁, "", h₁, h₂⟩
    rw [String.extract_eq_copy_slice _ _ hle, hr]
    simp
  | case3 acc start p h c hc ih =>
    intro t₁ r t₂ h₁ h₂
    obtain ⟨t₂', rfl⟩ := h₂.exists_eq_singleton_append h
    have h₂' := h₂.next
    obtain ⟨hle, hr⟩ := String.copy_slice_eq_iff_splits.mpr
      ⟨t₁, String.singleton (p.get h) ++ t₂', h₁, h₂⟩
    rw [ih (t₁ ++ r ++ String.singleton (p.get h)) "" t₂' (by simpa using h₂')
      (by simpa using h₂'), String.extract_eq_copy_slice _ _ hle, hr]
    simp [String.toList_append, c]
  | case4 acc start p h c hc ih =>
    intro t₁ r t₂ h₁ h₂
    obtain ⟨t₂', rfl⟩ := h₂.exists_eq_singleton_append h
    have h₂' := h₂.next
    rw [ih t₁ (r ++ String.singleton (p.get h)) t₂' (by rw [String.append_assoc]; exact h₁)
      (by rw [← String.append_assoc]; exact h₂'), String.toList_append, String.toList_singleton,
      List.singleton_append, List.foldl_cons,
      escapeCharTo_of_not_needsEscape _ (Bool.eq_false_iff.mpr hc), ← String.append_assoc,
      String.append_singleton]

/--
Escaping a string by stretches writes exactly what escaping it a character at a time writes.
Every claim tying string literals to the grammar is about `escapeTo`, and what runs is
`escapeToFast`; this makes them one program.

`@escapeTo = @escapeToFast` equates the functions over every accumulator and string, as
`@[csimp]` requires. `escapeToFast` starts the scan at the start of `s` with nothing pending,
where `escapeRunTo_eq` gives `s` folded through `escapeCharTo` onto `acc`, the definition of
`escapeTo`.
-/
@[csimp] theorem escapeTo_eq_escapeToFast : @escapeTo = @escapeToFast := by
  funext acc s
  rw [escapeToFast, escapeRunTo_eq s acc _ _ "" "" s (by simp) (by simp), escapeTo,
    String.foldl_eq_foldl_toList]
  simp

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

/-!
`render` builds each separator, break and closing bracket as a string of its own, appends each
number as a fresh string, and allocates a cell for every element and member it visits, once when an
array becomes a list and again on its stack. What runs for a single value writes all of its text
straight onto the accumulator and keeps one frame per open container, holding the container's
array and the index of the next entry, so an entry that is not a container costs an index step and
nothing on the heap.
-/

def spaceBlock : String := "".pushn ' ' 32

/-- `acc.pushn ' ' n`, appending whole blocks of spaces while there are many to write. -/
def pushSpaces (acc : String) (n : Nat) : String :=
  if n < 32 then acc.pushn ' ' n else pushSpaces (acc ++ spaceBlock) (n - 32)
termination_by n
decreasing_by omega

def Style.lineBreakTo (st : Style) (acc : String) (depth : Nat) : String :=
  match st.indent with
  | none => acc
  | some k =>
    -- The usual indentation is short, and is pushed without a call to `pushSpaces`.
    let n := k * depth
    if n < 32 then (acc.push '\n').pushn ' ' n else pushSpaces (acc.push '\n') n

def Style.precedesTo (st : Style) (acc : String) (depth : Nat) (first : Bool) : String :=
  if first then acc else st.lineBreakTo (acc.push ',') depth

def Style.colonTo (st : Style) (acc : String) : String :=
  match st.indent with
  | none => acc.push ':'
  | some _ => (acc.push ':').push ' '

def isScalar : Json → Bool
  | .arr _ | .obj _ => false
  | _ => true

/-- `acc` followed by `j`, for a `j` that `isScalar` accepts; a container is not written. -/
def scalarTo (acc : String) : Json → String
  | .null => acc ++ "null"
  | .bool true => acc ++ "true"
  | .bool false => acc ++ "false"
  | .num n => numberTo acc n
  | .str s => stringTo acc s
  | .arr _ | .obj _ => acc

/--
Writing spaces a block at a time appends exactly as many spaces as pushing them one by one. Deep
indentation is written this way, where one push per space would dominate the cost of `pretty`.

`(pushSpaces acc n).toList` is the text produced and `List.replicate n ' '` is `n` spaces; the
induction is strong recursion on `n`, taking off one block of 32 at each step.
-/
private theorem toList_pushSpaces (acc : String) (n : Nat) :
    (pushSpaces acc n).toList = acc.toList ++ List.replicate n ' ' := by
  induction n using Nat.strongRecOn generalizing acc with
  | ind n ih =>
    rw [pushSpaces]
    split
    · exact toList_pushn acc ' ' n
    · next h =>
      rw [ih (n - 32) (by omega), String.toList_append, spaceBlock, toList_pushn,
        List.append_assoc, String.toList_empty, List.nil_append, List.replicate_append_replicate]
      congr 2
      omega

/--
Writing a line break onto the accumulated text is appending the break `render` builds. The
compact form writes nothing, and the pretty form a newline and the indentation.

`st.lineBreakTo acc depth` is what the frame-based traversal produces and
`acc ++ st.lineBreak depth` what `render` produces; the proof takes the two layouts in turn.
-/
private theorem lineBreakTo_eq (st : Style) (acc : String) (depth : Nat) :
    st.lineBreakTo acc depth = acc ++ st.lineBreak depth := by
  rw [Style.lineBreakTo, Style.lineBreak]
  split
  · simp
  · rw [← String.toList_inj]
    simp only
    split <;> simp [toList_pushn, toList_pushSpaces, spaces]

/--
Writing a break and then a closing bracket onto the accumulated text is appending the closing text
`render` builds, the break followed by the bracket, without building that text as a string.

`(st.lineBreakTo acc depth).push c` is what the frame-based traversal produces and
`acc ++ (st.lineBreak depth ++ String.singleton c)` what `render` produces, in either layout.
-/
private theorem lineBreakTo_push (st : Style) (acc : String) (depth : Nat) (c : Char) :
    (st.lineBreakTo acc depth).push c = acc ++ (st.lineBreak depth ++ String.singleton c) := by
  rw [lineBreakTo_eq, ← String.toList_inj]; simp

/--
Writing the separator in front of an element or member is appending the one `render` builds:
nothing before the first, and a comma and a break before the others.

`st.precedesTo acc depth first` is the frame-based traversal's text and
`acc ++ st.precedes depth first` `render`'s, for either value of `first`.
-/
private theorem precedesTo_eq (st : Style) (acc : String) (depth : Nat) (first : Bool) :
    st.precedesTo acc depth first = acc ++ st.precedes depth first := by
  rw [Style.precedesTo, Style.precedes]
  split
  · simp
  · rw [lineBreakTo_eq, ← String.toList_inj]; simp

/--
Writing the colon after a member's name is appending the one `render` builds, with a space after
it in the pretty form.

`st.colonTo acc` is the frame-based traversal's text and `acc ++ st.colon` `render`'s, in both
layouts.
-/
private theorem colonTo_eq (st : Style) (acc : String) : st.colonTo acc = acc ++ st.colon := by
  rw [Style.colonTo, Style.colon]
  split <;> (rw [← String.toList_inj]; simp)

/--
A value that is not a container takes `render` one step, which appends its text. This is what
lets the frame-based traversal write such an element or member at once, with no frame of its own.

`h : isScalar j = true` excludes arrays and objects, the values whose step pushes more work instead
of writing text. The equation says rendering `j` and then `rest` is rendering `rest` after
`scalarTo` has written `j`, whatever the depth `d`.
-/
private theorem render_scalar (st : Style) (d : Nat) (j : Json) (rest : List Item) (acc : String)
    (h : isScalar j = true) :
    render st (.val d j :: rest) acc = render st rest (scalarTo acc j) := by
  match j, h with
  | .null, _ => rw [render, scalarTo]
  | .bool true, _ => rw [render, scalarTo]
  | .bool false, _ => rw [render, scalarTo]
  | .num n, _ => rw [render, scalarTo, numberTo_eq]
  | .str s, _ => rw [render, scalarTo]

/-- A container being written: its depth, its elements or members, and the index of the next. -/
inductive Frame where
  | arr (depth : Nat) (elems : Array Json) (i : Nat)
  | obj (depth : Nat) (fields : Array (String × Json)) (i : Nat)

/-- The pending items that a stack of frames stands for. -/
def Frame.items (st : Style) : List Frame → List Item
  | [] => []
  | .arr d a i :: rest =>
    .elems (d + 1) (a.toList.drop i) (i == 0) :: .lit (st.lineBreak d ++ "]") :: Frame.items st rest
  | .obj d f i :: rest =>
    .members (d + 1) (f.toList.drop i) (i == 0) :: .lit (st.lineBreak d ++ "}") ::
      Frame.items st rest

/--
An index inside an array marks where its list of entries continues: the entry at that index, then
those after it. The frame-based traversal steps an index where `render` takes a list apart, and
this is what lets the two be compared.

`h : i < a.size` says the index is in range, which is what makes `a[i]` exist; the equation splits
the entries from `i` on into `a[i]` and the entries from `i + 1` on.
-/
private theorem drop_toList_cons {α : Type} (a : Array α) (i : Nat) (h : i < a.size) :
    a.toList.drop i = a[i] :: a.toList.drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

/--
The measure of a list of members counts each member's value and its separator, whatever the
member's name. The traversal's termination is argued over members given as pairs, not taken apart
into a name and a value.

`sizeFields (p :: l)` is the measure of the members `p` followed by `l`, and the equation gives it
as `p`'s value's measure, one for the separator, and the rest.
-/
private theorem sizeFields_cons (p : String × Json) (l : List (String × Json)) :
    sizeFields (p :: l) = size p.2 + 1 + sizeFields l := by
  cases p; rfl

def renderFrames (st : Style) : List Frame → String → String
  | [], acc => acc
  | .arr d a i :: rest, acc =>
    if h : i < a.size then
      let acc := st.precedesTo acc (d + 1) (i == 0)
      match hj : a[i] with
      | .arr b =>
        if b.isEmpty then
          renderFrames st (.arr d a (i + 1) :: rest) (acc ++ "[]")
        else
          renderFrames st (.arr (d + 1) b 0 :: .arr d a (i + 1) :: rest)
            (st.lineBreakTo (acc.push '[') (d + 2))
      | .obj g =>
        if g.isEmpty then
          renderFrames st (.arr d a (i + 1) :: rest) (acc ++ "{}")
        else
          renderFrames st (.obj (d + 1) g 0 :: .arr d a (i + 1) :: rest)
            (st.lineBreakTo (acc.push '{') (d + 2))
      | j => renderFrames st (.arr d a (i + 1) :: rest) (scalarTo acc j)
    else
      renderFrames st rest ((st.lineBreakTo acc d).push ']')
  | .obj d f i :: rest, acc =>
    if h : i < f.size then
      let acc := st.colonTo (stringTo (st.precedesTo acc (d + 1) (i == 0)) f[i].1)
      match hv : f[i].2 with
      | .arr b =>
        if b.isEmpty then
          renderFrames st (.obj d f (i + 1) :: rest) (acc ++ "[]")
        else
          renderFrames st (.arr (d + 1) b 0 :: .obj d f (i + 1) :: rest)
            (st.lineBreakTo (acc.push '[') (d + 2))
      | .obj g =>
        if g.isEmpty then
          renderFrames st (.obj d f (i + 1) :: rest) (acc ++ "{}")
        else
          renderFrames st (.obj (d + 1) g 0 :: .obj d f (i + 1) :: rest)
            (st.lineBreakTo (acc.push '{') (d + 2))
      | v => renderFrames st (.obj d f (i + 1) :: rest) (scalarTo acc v)
    else
      renderFrames st rest ((st.lineBreakTo acc d).push '}')
termination_by frames _ => weight (Frame.items st frames)
decreasing_by
  all_goals
    simp only [Frame.items, weight, Item.weight, List.drop_zero]
    first
    | omega
    | (rw [drop_toList_cons _ _ h]; simp only [sizeList]; omega)
    | (rw [drop_toList_cons _ _ h]; simp only [sizeList, hj, size]; omega)
    | (rw [drop_toList_cons _ _ h]; simp only [sizeFields_cons]; omega)
    | (rw [drop_toList_cons _ _ h]; simp only [sizeFields_cons, hv, size]; omega)

/-- `render`, through frames when the stack holds a single container. -/
def renderTop (st : Style) (items : List Item) (acc : String) : String :=
  match items with
  | [.val d (.arr a)] =>
    if a.isEmpty then acc ++ "[]"
    else renderFrames st [.arr d a 0] (st.lineBreakTo (acc.push '[') (d + 1))
  | [.val d (.obj f)] =>
    if f.isEmpty then acc ++ "{}"
    else renderFrames st [.obj d f 0] (st.lineBreakTo (acc.push '{') (d + 1))
  | items => render st items acc

/--
A value that is neither an array nor an object is one `isScalar` accepts. The frame-based
traversal tells containers apart by matching on them, and this turns the cases it falls through
to into the condition `render_scalar` asks for.

`h₁` and `h₂` say `j` is not an array and not an object; the conclusion is `isScalar j = true`,
checked constructor by constructor.
-/
private theorem isScalar_of_ne {j : Json} (h₁ : ∀ b, j = .arr b → False)
    (h₂ : ∀ g, j = .obj g → False) : isScalar j = true := by
  cases j with
  | arr b => exact (h₁ b rfl).elim
  | obj g => exact (h₂ g rfl).elim
  | _ => rfl

/--
`render` takes the entry at an index off the elements that remain from it, so a frame's next step
and `render`'s next step agree on which element comes next.

`h : i < a.size` says there is an element at `i`. The equation unfolds one step of `render` on the
elements from `i` on, which writes the separator and leaves the element at `i` to render, followed
by the elements from `i + 1`, none of them first.
-/
private theorem render_elems_drop (st : Style) (d : Nat) (a : Array Json) (i : Nat)
    (h : i < a.size) (first : Bool) (rest : List Item) (acc : String) :
    render st (.elems d (a.toList.drop i) first :: rest) acc =
      render st (.val d a[i] :: .elems d (a.toList.drop (i + 1)) false :: rest)
        (acc ++ st.precedes d first) := by
  rw [drop_toList_cons _ _ h, render]

/--
`render` takes the member at an index off the members that remain from it, writing its name and
colon, so a frame's next step and `render`'s next step agree on which member comes next.

`h : i < f.size` says there is a member at `i`. The equation unfolds one step of `render` on the
members from `i` on: the separator, the name `f[i].1` as a string literal and the colon are
written, and the value `f[i].2` is left to render, followed by the members from `i + 1`.
-/
private theorem render_members_drop (st : Style) (d : Nat) (f : Array (String × Json)) (i : Nat)
    (h : i < f.size) (first : Bool) (rest : List Item) (acc : String) :
    render st (.members d (f.toList.drop i) first :: rest) acc =
      render st (.val d f[i].2 :: .members d (f.toList.drop (i + 1)) false :: rest)
        (stringTo (acc ++ st.precedes d first) f[i].1 ++ st.colon) := by
  rw [drop_toList_cons _ _ h]
  generalize f[i] = p
  obtain ⟨k, v⟩ := p
  rw [render]

/--
An array whose elements have all been written closes with its bracket, which is what `render`
does when the elements from the frame's index on are none.

`h : l.length ≤ i` says the index has reached the end of the elements `l`. The equation says
`render` then writes `close` and carries on with `rest`.
-/
private theorem render_elems_done (st : Style) (d i : Nat) (l : List Json) (h : l.length ≤ i)
    (first : Bool) (close : String) (rest : List Item) (acc : String) :
    render st (.elems d (l.drop i) first :: .lit close :: rest) acc =
      render st rest (acc ++ close) := by
  rw [List.drop_eq_nil_of_le h, render, render]

/--
An object whose members have all been written closes with its bracket, which is what `render`
does when the members from the frame's index on are none.

`h : l.length ≤ i` says the index has reached the end of the members `l`. The equation says
`render` then writes `close` and carries on with `rest`.
-/
private theorem render_members_done (st : Style) (d i : Nat) (l : List (String × Json))
    (h : l.length ≤ i) (first : Bool) (close : String) (rest : List Item) (acc : String) :
    render st (.members d (l.drop i) first :: .lit close :: rest) acc =
      render st rest (acc ++ close) := by
  rw [List.drop_eq_nil_of_le h, render, render]

/--
The frame-based traversal writes exactly what `render` writes from the items the frames stand for.
Stating it for every stack of frames and every accumulator is what makes it an induction
hypothesis.

`renderFrames st frames acc` is the frame-based traversal and
`render st (Frame.items st frames) acc` is `render` on the corresponding items: each frame stands
for its remaining entries, from its index on, followed by its closing bracket. The induction
follows `renderFrames`, matching each of its steps with the steps `render` takes on the same entry.
-/
private theorem renderFrames_eq (st : Style) (frames : List Frame) (acc : String) :
    renderFrames st frames acc = render st (Frame.items st frames) acc := by
  have hsucc : ∀ i : Nat, (i + 1 == 0) = false := fun i => by simp
  fun_induction renderFrames st frames acc with
  | case1 => rw [Frame.items, render]
  | case2 d a i rest acc₀ h acc b hj hb ih =>
    rw [ih, Frame.items, Frame.items, render_elems_drop st _ a i h, hj]
    conv => rhs; rw [render, ite_eq_left hb]
    simp only [acc, precedesTo_eq, hsucc]
  | case3 d a i rest acc₀ h acc b hj hb ih =>
    rw [ih, Frame.items, Frame.items, Frame.items, render_elems_drop st _ a i h, hj]
    conv => rhs; rw [render, ite_eq_right hb]
    rw [lineBreakTo_eq, ← String.append_singleton]
    simp only [acc, precedesTo_eq, hsucc, List.drop_zero]
    rfl
  | case4 d a i rest acc₀ h acc g hj hg ih =>
    rw [ih, Frame.items, Frame.items, render_elems_drop st _ a i h, hj]
    conv => rhs; rw [render, ite_eq_left hg]
    simp only [acc, precedesTo_eq, hsucc]
  | case5 d a i rest acc₀ h acc g hj hg ih =>
    rw [ih, Frame.items, Frame.items, Frame.items, render_elems_drop st _ a i h, hj]
    conv => rhs; rw [render, ite_eq_right hg]
    rw [lineBreakTo_eq, ← String.append_singleton]
    simp only [acc, precedesTo_eq, hsucc, List.drop_zero]
    rfl
  | case6 d a i rest acc₀ h acc h₁ h₂ ih =>
    rw [ih, Frame.items, Frame.items, render_elems_drop st _ a i h,
      render_scalar _ _ _ _ _ (isScalar_of_ne h₁ h₂)]
    simp only [acc, precedesTo_eq, hsucc]
  | case7 d a i rest acc h ih =>
    rw [ih, Frame.items, render_elems_done st _ i _ (by simpa using h), lineBreakTo_push]
    rfl
  | case8 d f i rest acc₀ h acc b hv hb ih =>
    rw [ih, Frame.items, Frame.items, render_members_drop st _ f i h, hv]
    conv => rhs; rw [render, ite_eq_left hb]
    simp only [acc, precedesTo_eq, colonTo_eq, hsucc]
  | case9 d f i rest acc₀ h acc b hv hb ih =>
    rw [ih, Frame.items, Frame.items, Frame.items, render_members_drop st _ f i h, hv]
    conv => rhs; rw [render, ite_eq_right hb]
    rw [lineBreakTo_eq, ← String.append_singleton]
    simp only [acc, precedesTo_eq, colonTo_eq, hsucc, List.drop_zero]
    rfl
  | case10 d f i rest acc₀ h acc g hv hg ih =>
    rw [ih, Frame.items, Frame.items, render_members_drop st _ f i h, hv]
    conv => rhs; rw [render, ite_eq_left hg]
    simp only [acc, precedesTo_eq, colonTo_eq, hsucc]
  | case11 d f i rest acc₀ h acc g hv hg ih =>
    rw [ih, Frame.items, Frame.items, Frame.items, render_members_drop st _ f i h, hv]
    conv => rhs; rw [render, ite_eq_right hg]
    rw [lineBreakTo_eq, ← String.append_singleton]
    simp only [acc, precedesTo_eq, colonTo_eq, hsucc, List.drop_zero]
    rfl
  | case12 d f i rest acc₀ h acc h₁ h₂ ih =>
    rw [ih, Frame.items, Frame.items, render_members_drop st _ f i h,
      render_scalar _ _ _ _ _ (isScalar_of_ne h₁ h₂)]
    simp only [acc, precedesTo_eq, colonTo_eq, hsucc]
  | case13 d f i rest acc h ih =>
    rw [ih, Frame.items, render_members_done st _ i _ (by simpa using h), lineBreakTo_push]
    rfl

/--
Compiled code renders through `renderTop`. Every claim tying the printer to the grammar is about
`render`, and this makes the two one program, for `compress` and `pretty` alike.

`@render = @renderTop` equates the functions over every layout, stack and accumulator, as
`@[csimp]` requires. A single container goes through `renderFrames` and `renderFrames_eq`; any
other stack is left to `render` itself, which `renderTop` was compiled against before this lemma
existed.
-/
@[csimp] theorem render_eq_renderTop : @render = @renderTop := by
  funext st items acc
  unfold renderTop
  split
  · next d a =>
    split
    · next h => rw [render, ite_eq_left h, render]
    · next h =>
      rw [renderFrames_eq, Frame.items, Frame.items, render, ite_eq_right h, lineBreakTo_eq,
        ← String.append_singleton]
      rfl
  · next d f =>
    split
    · next h => rw [render, ite_eq_left h, render]
    · next h =>
      rw [renderFrames_eq, Frame.items, Frame.items, render, ite_eq_right h, lineBreakTo_eq,
        ← String.append_singleton]
      rfl
  · rfl

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
