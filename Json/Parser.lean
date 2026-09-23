/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Spec

public section

namespace Json

/-!
Reading text into a value.

`parse` takes a `String` and `parseBytes` a `ByteArray`, which is where the UTF-8 that RFC 8259
requires is enforced, by the verified decoder in `Init.Data.String.Decode`. Text that is not one
complete value is an error rather than a partial value, and an error says what was wrong and
where.

The defaults are the strict readings, and none of them is a crash guard, the machine keeping its
stack on the heap: a repeated field name is refused, nesting beyond 1024 is refused, and a
significand of more than a thousand digits is refused unread. `Config` turns off any of the
three. What no configuration relaxes is the refusal of a lone surrogate, which denotes no
sequence of code points at all.
-/

/-- What to do when an object names the same field twice. -/
inductive DuplicateKeys where
  | reject
  | allow
deriving DecidableEq, Repr

/-- How strictly to read. Every default here is the strict reading. -/
structure Config where
  /--
  Rejecting is the default because the RFC leaves the outcome unspecified, so accepting exposes
  the difference between two implementations reading the same bytes.
  -/
  duplicateKeys : DuplicateKeys := .reject
  /--
  A limit on nesting, as policy rather than as protection: the parser keeps its work on the heap,
  so `none` is safe and bounded only by memory.
  -/
  maxDepth : Option Nat := some 1024
  /--
  A limit on the digits of a significand or an exponent. `none` costs no more than the digits
  are worth: both reading and writing a long one halve rather than working a digit at a time.
  -/
  maxNumberDigits : Option Nat := some 1000
  /-- RFC 8259 permits ignoring a leading `U+FEFF` in text that was not networked. -/
  ignoreBOM : Bool := true
deriving Repr

/-- Why a text was refused. `describe` renders one as a sentence. -/
inductive ErrorKind where
  | unexpectedEnd
  | unexpectedChar (c : Char)
  | trailingText (c : Char)
  | controlCharInString (c : Char)
  | unknownEscape (c : Char)
  | badHexEscape
  | loneSurrogate
  | expectedDigit
  | duplicateKey (name : String)
  | depthExceeded
  | tooManyDigits
  | invalidUtf8
deriving DecidableEq, Repr

/-- A failure, with the byte offset into the text at which it was detected. -/
structure Error where
  byteOffset : Nat
  kind : ErrorKind
deriving DecidableEq, Repr

/-- A description fit for a user, rather than the constructor's `Repr`. -/
def ErrorKind.describe : ErrorKind → String
  | unexpectedEnd => "unexpected end of input"
  | unexpectedChar c => s!"unexpected character {repr c}"
  | trailingText c => s!"unexpected text after the value, starting with {repr c}"
  | controlCharInString c =>
    s!"a string holds the control character {repr c}, which has to be escaped"
  | unknownEscape c => s!"unknown escape \\{c}"
  | badHexEscape => "a \\u escape needs four hexadecimal digits"
  | loneSurrogate => "a \\u escape denotes half of a surrogate pair, with no partner beside it"
  | expectedDigit => "expected a digit"
  -- A field name arrives from the input, so a long one is not repeated back.
  | duplicateKey name =>
    if name.length ≤ 40 then s!"the field name {repr name} appears twice"
    else "a field name appears twice"
  | depthExceeded => "nesting deeper than the configured limit"
  | tooManyDigits => "a number with more digits than the configured limit"
  | invalidUtf8 => "the input is not valid UTF-8"

instance : ToString ErrorKind := ⟨ErrorKind.describe⟩

instance : ToString Error := ⟨fun e => s!"{e.kind.describe} at byte {e.byteOffset}"⟩


namespace Parser

@[expose] section

/-!
The scanner walks the text by position rather than converting it to a list of characters first.
That conversion cost about thirty bytes for every byte of input, which put a limit on the size of
document that could safely be read; a position costs nothing, so what a parse holds is the text
and the value.
-/

section
variable {s : String}

/-- Where a position is, as a byte offset, which is what an error reports. -/
def byteOffset (p : s.Pos) : Nat := p.offset.byteIdx

/-- The character at `p` and the position after it, or nothing at the end of the text. -/
@[inline]
def step? (p : s.Pos) : Option (Char × s.Pos) :=
  if h : p = s.endPos then none else some (p.get h, p.next h)

/--
Reading one character always leaves less text to read. The whole parser walks a `String.Pos`
rather than a list, so it has no structurally smaller argument to recurse on; this is the measure
every one of its termination arguments is ultimately built from, and without it none of `skipWs`,
`string`, `digits` or the value machine could be written without `partial`.

`h : step? p = some (c, q)` says there was a character `c` at `p` and `q` is the position just
past it. `remainingBytes` counts the bytes from a position to the end of the text, and
`q.remainingBytes < p.remainingBytes` says that count strictly fell. The `none` case of `step?`,
where `p` is already the end, cannot arise under `h`, which is what makes the inequality strict
rather than merely non-strict.
-/
theorem step?_lt {p q : s.Pos} {c : Char} (h : step? p = some (c, q)) :
    q.remainingBytes < p.remainingBytes := by
  rw [step?] at h
  split at h
  · simp at h
  · rw [Option.some.injEq, Prod.mk.injEq] at h
    exact (String.Pos.lt_iff_remainingBytes_lt _ _).mp (h.2 ▸ String.Pos.lt_next)

/--
A scan that consumed at least one character. Carrying the proof here rather than proving it
afterwards keeps the machine's termination argument to one line per call.
-/
structure Scanned (α : Type) (start : s.Pos) where
  value : α
  pos : s.Pos
  consumed : pos.remainingBytes < start.remainingBytes

/-- A scan that may have consumed nothing, as whitespace and the optional productions can. -/
structure Consumed (α : Type) (start : s.Pos) where
  value : α
  pos : s.Pos
  notLonger : pos.remainingBytes ≤ start.remainingBytes

/-! ## Leaf scanners -/

/--
Whitespace, if there is any.

Written as a loop over a position that carries how far it has come, rather than as a recursion
whose result is rebuilt on the way out, so that a long run costs no stack and holds nothing per
character.
-/
def skipWs (start : s.Pos) : Consumed Unit start := go start (Nat.le_refl _)
where
  go (p : s.Pos) (h : p.remainingBytes ≤ start.remainingBytes) : Consumed Unit start :=
    match hc : step? p with
    | some (c, q) =>
      if Spec.isWs c then go q (by have := step?_lt hc; omega)
      else ⟨(), p, h⟩
    | none => ⟨(), p, h⟩
  termination_by p.remainingBytes
  decreasing_by exact step?_lt hc

/-- The characters of `l` in order, if the text at `p` begins with them. -/
def expect? (p : s.Pos) : List Char → Option (Consumed Unit p)
  | [] => some ⟨(), p, Nat.le_refl _⟩
  | c :: rest =>
    match hc : step? p with
    | some (c', q) =>
      if c == c' then
        match expect? q rest with
        | some r => some ⟨(), r.pos, by have := r.notLonger; have := step?_lt hc; omega⟩
        | none => none
      else none
    | none => none

/-- One hexadecimal digit, as a number. -/
def hexDigit? (p : s.Pos) : Option (Scanned Nat p) :=
  match hc : step? p with
  | some (c, q) =>
    match Spec.hexVal? c with
    | some v => some ⟨v, q, step?_lt hc⟩
    | none => none
  | none => none

/-- `4HEXDIG`, the body of a `\u` escape. -/
def hex4? (p : s.Pos) : Option (Scanned Nat p) :=
  match hexDigit? p with
  | none => none
  | some r₁ =>
    match hexDigit? r₁.pos with
    | none => none
    | some r₂ =>
      match hexDigit? r₂.pos with
      | none => none
      | some r₃ =>
        match hexDigit? r₃.pos with
        | none => none
        | some r₄ =>
          some ⟨r₁.value * 4096 + r₂.value * 256 + r₃.value * 16 + r₄.value, r₄.pos, by
            have := r₁.consumed; have := r₂.consumed; have := r₃.consumed; have := r₄.consumed
            omega⟩

/-- A whole `\uXXXX` escape, which is how the low half of a surrogate pair is looked for. -/
def escapeHex4? (p : s.Pos) : Option (Scanned Nat p) :=
  match hc : step? p with
  | some ('\\', q) =>
    match hu : step? q with
    | some ('u', r) =>
      match hex4? r with
      | some h =>
        some ⟨h.value, h.pos, by
          have := h.consumed; have := step?_lt hc; have := step?_lt hu; omega⟩
      | none => none
    | _ => none
  | _ => none

/-- The two-character escapes, which do not include `u`. -/
def escapeChar? (c : Char) : Option Char :=
  if c == '"' then some '"'
  else if c == '\\' then some '\\'
  else if c == '/' then some '/'
  else if c == 'b' then some '\x08'
  else if c == 'f' then some '\x0c'
  else if c == 'n' then some '\n'
  else if c == 'r' then some '\x0d'
  else if c == 't' then some '\t'
  else none

/-- A code point that is neither a surrogate nor out of range. -/
def charOfCodePoint? (v : Nat) : Option Char :=
  if h : (UInt32.ofNat v).isValidChar then some ⟨UInt32.ofNat v, h⟩ else none

def combineSurrogates (hi lo : Nat) : Nat :=
  0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00)

/--
What the next piece of a string is: its end, one character of it, or a failure. Reading a piece
and recursing once keeps `string` to a single recursive call, and so to a one-line termination
argument, where the escapes would otherwise each need their own.
-/
inductive StringStep (s : String) where
  | done (pos : s.Pos)
  | char (c : Char) (pos : s.Pos)
  | fail (e : Error)

/--
One piece of a string, starting at `p`, which is either just after the opening quotation mark or
just after the last piece.

An unpaired surrogate escape is an error rather than a replacement character, so text that cannot
be represented is never silently altered.
-/
def stringStep (p : s.Pos) : StringStep s :=
  match step? p with
  | none => .fail ⟨byteOffset p, .unexpectedEnd⟩
  | some ('"', q) => .done q
  | some ('\\', q) =>
    match step? q with
    | none => .fail ⟨byteOffset q, .unexpectedEnd⟩
    | some ('u', r) =>
      match hex4? r with
      | none => .fail ⟨byteOffset r, .badHexEscape⟩
      | some h =>
        if h.value < 0xD800 || 0xDFFF < h.value then
          match charOfCodePoint? h.value with
          | none => .fail ⟨byteOffset r, .badHexEscape⟩
          | some c => .char c h.pos
        else if h.value ≤ 0xDBFF then
          match escapeHex4? h.pos with
          | none => .fail ⟨byteOffset r, .loneSurrogate⟩
          | some lo =>
            if 0xDC00 ≤ lo.value && lo.value ≤ 0xDFFF then
              match charOfCodePoint? (combineSurrogates h.value lo.value) with
              | none => .fail ⟨byteOffset r, .badHexEscape⟩
              | some c => .char c lo.pos
            else
              .fail ⟨byteOffset r, .loneSurrogate⟩
        else
          .fail ⟨byteOffset r, .loneSurrogate⟩
    | some (c, r) =>
      match escapeChar? c with
      | none => .fail ⟨byteOffset q, .unknownEscape c⟩
      | some ch => .char ch r
  | some (c, q) =>
    if Spec.isUnescaped c then .char c q
    else .fail ⟨byteOffset p, .controlCharInString c⟩

/--
Finding the closing quotation mark of a string moves past it. `string` loops until `stringStep`
reports the end, so the loop's measure has to fall on that step as well as on the ones that
produce characters; this is that half.

`stringStep p = .done q` says the piece read at `p` was the closing quotation mark and `q` is the
position after it. The conclusion `q.remainingBytes < p.remainingBytes` says the text left to read
strictly shrank. `.done` is produced by exactly one branch, the one that consumed a `"` through
`step?`, so the claim reduces to `step?_lt`; every other branch makes the hypothesis unsatisfiable
rather than the conclusion true.
-/
theorem stringStep_done_lt (p : s.Pos) :
    ∀ q, stringStep p = .done q → q.remainingBytes < p.remainingBytes := by
  fun_cases stringStep p with
  | case2 w hc =>
    intro q h
    injection h with h
    subst h
    exact step?_lt hc
  | _ => intro q h; simp at h

/--
Producing one character of a string consumes at least one character of the text. This is what
makes `string` terminate: each turn of its loop appends a character and moves on, so the bytes
remaining fall even where an escape stands for a character that was never literally there.

`stringStep p = .char c q` says the piece read at `p` yielded the character `c` and left `q`. The
conclusion `q.remainingBytes < p.remainingBytes` says the remaining text strictly shrank. Four
branches produce `.char`: an unescaped character, a two-character escape, a `\u` escape, and a
surrogate pair; each consumes at least the `step?` the proof appeals to, and the longer ones
consume more, so no way of spelling a character consumes nothing.
-/
theorem stringStep_char_lt (p : s.Pos) :
    ∀ c q, stringStep p = .char c q → q.remainingBytes < p.remainingBytes := by
  fun_cases stringStep p with
  | case6 w hc r hu hex hx _ ch hcp =>
    intro c q h
    injection h with _ h
    subst h
    have := hex.consumed
    have := step?_lt hc
    have := step?_lt hu
    omega
  | case9 w hc r hu hex hx _ _ lo hlo _ ch hcp =>
    intro c q h
    injection h with _ h
    subst h
    have := lo.consumed
    have := hex.consumed
    have := step?_lt hc
    have := step?_lt hu
    omega
  | case13 w hc e r _ hu ch he =>
    intro c q h
    injection h with _ h
    subst h
    have := step?_lt hc
    have := step?_lt hu
    omega
  | case14 e w _ _ hc _ =>
    intro c q h
    injection h with _ h
    subst h
    exact step?_lt hc
  | _ => intro c q h; simp at h

def string (start : s.Pos) (acc : String) : Except Error (Scanned String start) :=
  go start acc (Nat.le_refl _)
where
  go (p : s.Pos) (acc : String) (h : p.remainingBytes ≤ start.remainingBytes) :
      Except Error (Scanned String start) :=
    match hs : stringStep p with
    | .fail e => .error e
    | .done q => .ok ⟨acc, q, by have := stringStep_done_lt p q hs; omega⟩
    | .char c q => go q (acc.push c) (by have := stringStep_char_lt p c q hs; omega)
  termination_by p.remainingBytes
  decreasing_by exact stringStep_char_lt p c q hs

/-! ## Numbers -/

/-- `*DIGIT`, accumulating the most significant digit first, and as a loop for the same reason. -/
def digits (start : s.Pos) (value count : Nat) : Consumed (Nat × Nat) start :=
  go start value count (Nat.le_refl _)
where
  go (p : s.Pos) (value count : Nat) (h : p.remainingBytes ≤ start.remainingBytes) :
      Consumed (Nat × Nat) start :=
    match hc : step? p with
    | some (c, q) =>
      if Spec.isDigit c then
        go q (value * 10 + Spec.digitVal c) (count + 1) (by have := step?_lt hc; omega)
      else
        ⟨(value, count), p, h⟩
    | none => ⟨(value, count), p, h⟩
  termination_by p.remainingBytes
  decreasing_by exact step?_lt hc

/-!
Reading `d₀d₁…dₙ` as `((d₀ * 10 + d₁) * 10 + …)` multiplies an ever longer number by a short one,
which costs a time quadratic in the digits and is why a limit on them was ever needed. Halving
instead keeps the two sides of each multiplication the same length, which is what
arbitrary-precision multiplication is fast at. The loop above is the one the proofs are stated
against, and the two are proved equal, so what runs is the halving one.
-/

/-- A run of digits, as the number it denotes and how many there are. -/
def digitJoin (a b : Nat × Nat) : Nat × Nat := (a.1 * 10 ^ b.2 + b.1, a.2 + b.2)

def digitStep (a : Nat × Nat) (d : Nat) : Nat × Nat := (a.1 * 10 + d, a.2 + 1)

/--
Splitting a run of digits into pieces and joining the pieces back up gives the same number
whatever way the split was made. That is what allows the halving reader to be recognised as the
one-digit-at-a-time reader: the two differ only in how they associate the joins.

`digitJoin a b` places `a` above `b`, as `a.1 * 10 ^ b.2 + b.1` digits with `a.2 + b.2` of them,
so its second component is a length and its first the number those digits spell. The equation
`digitJoin (digitJoin a b) c = digitJoin a (digitJoin b c)` says joining the left pair first and
joining the right pair first agree. The lengths agree by arithmetic on `+`; the values agree
because `10 ^ (b.2 + c.2)` factors as `10 ^ b.2 * 10 ^ c.2`, which is what makes the two
placements of `a` the same shift.
-/
private theorem digitJoin_assoc (a b c : Nat × Nat) :
    digitJoin (digitJoin a b) c = digitJoin a (digitJoin b c) := by
  simp only [digitJoin, Prod.mk.injEq]
  refine ⟨?_, by omega⟩
  rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add, Nat.add_assoc]

/--
Appending one digit is joining a run of length one, so the accumulating loop is a special case of
the splitting reader rather than a different computation. Every step from the loop to the halving
form goes through this reading.

`digitStep a d = (a.1 * 10 + d, a.2 + 1)` is what the loop does to its accumulator on reading the
digit `d`. `digitJoin a (d, 1)` places the one-digit run `(d, 1)` below `a`, giving
`a.1 * 10 ^ 1 + d` with `a.2 + 1` digits. The two are the same term once `10 ^ 1` is `10`.
-/
private theorem digitStep_eq (a : Nat × Nat) (d : Nat) : digitStep a d = digitJoin a (d, 1) := by
  simp [digitStep, digitJoin]

/--
A run of digits contributes the same thing wherever the accumulator it is folded into came from:
folding into `a` is folding into nothing and then joining the result below `a`. This is what lets
a fold be cut at any point, which is what turning it into a divide-and-conquer needs.

`ds.foldl digitStep a` reads the digits `ds` left to right into the accumulator `a`.
`digitJoin a (ds.foldl digitStep (0, 0))` instead reads them into the empty accumulator and places
`a` above the result. The induction is on `ds` with `a` generalised, since each step changes the
accumulator, and `digitJoin_assoc` is what closes it.
-/
private theorem foldl_digitStep (ds : List Nat) (a : Nat × Nat) :
    ds.foldl digitStep a = digitJoin a (ds.foldl digitStep (0, 0)) := by
  induction ds generalizing a with
  | nil => simp [digitJoin]
  | cons d rest ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (digitStep (0, 0) d), digitStep_eq,
      digitStep_eq, ← digitJoin_assoc]
    simp [digitJoin]

def fromDigits : List Nat → Nat × Nat
  | [] => (0, 0)
  | [d] => (d, 1)
  | d₁ :: d₂ :: rest =>
    let ds := d₁ :: d₂ :: rest
    digitJoin (fromDigits (ds.take (ds.length / 2))) (fromDigits (ds.drop (ds.length / 2)))
termination_by ds => ds.length
decreasing_by
  · simp only [List.length_take, List.length_cons]
    omega
  · simp only [List.length_drop, List.length_cons]
    omega

/--
The halving reader and the one-digit-at-a-time reader compute the same pair. `fromDigits` is what
runs, because multiplying two numbers of similar length is what arbitrary-precision arithmetic is
fast at, while the loop multiplies an ever longer number by ten; every proof is stated against the
loop, and this is the bridge.

`fromDigits ds` splits `ds` in half, reads each half and joins them; `ds.foldl digitStep (0, 0)`
reads the digits one at a time from an empty accumulator. Both yield a value and a digit count.
The induction follows `fromDigits`' own recursion, and `foldl_digitStep` supplies the step: a fold
over `take ++ drop` is the fold over each half joined, which is exactly the split.
-/
private theorem fromDigits_eq (ds : List Nat) : fromDigits ds = ds.foldl digitStep (0, 0) := by
  fun_induction fromDigits ds with
  | case1 => simp
  | case2 d => simp [digitStep]
  | case3 _ _ _ l ih₁ ih₂ =>
    rw [ih₁, ih₂, ← foldl_digitStep, ← List.foldl_append, List.take_append_drop]

/-- The same run of digits, kept as a list, most recently read first. -/
def digitList (start p : s.Pos) (acc : List Nat)
    (h : p.remainingBytes ≤ start.remainingBytes) : Consumed (List Nat) start :=
  match hc : step? p with
  | some (c, q) =>
    if Spec.isDigit c then
      digitList start q (Spec.digitVal c :: acc) (by have := step?_lt hc; omega)
    else
      ⟨acc, p, h⟩
  | none => ⟨acc, p, h⟩
termination_by p.remainingBytes
decreasing_by exact step?_lt hc

def digitsFast (start : s.Pos) (value count : Nat) : Consumed (Nat × Nat) start :=
  match digitList start start [] (Nat.le_refl _) with
  | ⟨ds, pos, h⟩ => ⟨digitJoin (value, count) (fromDigits ds.reverse), pos, h⟩

/--
One turn of the digit loop reads one digit and carries on from the next position. `digits.go`
carries a proof that it has not overrun, so the loop cannot simply be unfolded by `rw`; this
states the unfolding as an equation between the two calls, with the bookkeeping argument on each
side left free.

`hc` says `c` is the character at `p` and `q` the position after it, and `hd` says `c` is a digit.
The equation then relates `digits.go start p v n h`, the loop at `p` holding value `v` and count
`n`, to `digits.go start q (v * 10 + Spec.digitVal c) (n + 1) h'`, the loop at `q` with the digit
folded in. `h` and `h'` are the proofs that `p` and `q` have not passed `start`; they carry no
information beyond their statements, so having a different one on each side is immaterial.
-/
private theorem digits_go_step {start p q : s.Pos} {c : Char} (hc : step? p = some (c, q))
    (hd : Spec.isDigit c = true) (v n : Nat) (h : p.remainingBytes ≤ start.remainingBytes)
    (h' : q.remainingBytes ≤ start.remainingBytes) :
    digits.go start p v n h = digits.go start q (v * 10 + Spec.digitVal c) (n + 1) h' := by
  rw [digits.go]
  split
  · next c' q' hc' =>
    rw [hc] at hc'
    injection hc' with hc''
    injection hc'' with h₁ h₂
    subst h₁
    subst h₂
    rw [ite_eq_left hd]
  · next hc' => rw [hc] at hc'; exact absurd hc' (by simp)

/--
The digit loop stops where the digits do, returning what it has accumulated and the position it
stopped at. The loop has two ways to end, at a non-digit and at the end of the text, and this
covers both, so no case analysis on which of them occurred is needed at the point of use.

`hstop` says that whatever character `step?` finds at `p`, if any, is not a digit; the vacuous
case, where `step?` returns `none`, is the end of the text and is covered by the same hypothesis.
The conclusion `digits.go start p v n h = ⟨(v, n), p, h⟩` says the loop returns its
accumulated value and count unchanged, and the position `p` it was called at.
-/
private theorem digits_go_stop {start p : s.Pos} (v n : Nat)
    (h : p.remainingBytes ≤ start.remainingBytes)
    (hstop : ∀ c q, step? p = some (c, q) → Spec.isDigit c = false) :
    digits.go start p v n h = ⟨(v, n), p, h⟩ := by
  rw [digits.go]
  split
  · next c' q' hc' => rw [ite_eq_right (by simp [hstop c' q' hc'])]
  · rfl

/--
The loop and the list-then-halve reader agree at every position, not merely at the start. Both
walk the same digits, but one folds as it goes and the other keeps the digits and reads them
afterwards, so they can only be compared in a form general enough to be an induction hypothesis:
this is that form, with the accumulator and the starting position both free.

`acc` is the digits already collected, most recent first, so `fromDigits acc.reverse` is what they
spell and `digitJoin (v, c) (fromDigits acc.reverse)` is the loop's accumulator at the same point.
The equation says the loop started there ends with the value, position and bound that `digitList`
reports, read through the same `digitJoin`. The induction follows `digitList`, whose three cases
are a digit read, a non-digit, and the end of the text; `digits_go_step` handles the first and
`digits_go_stop` the other two.
-/
private theorem digits_go_eq (start : s.Pos) (v c : Nat) :
    ∀ (p : s.Pos) (acc : List Nat) (h : p.remainingBytes ≤ start.remainingBytes),
      digits.go start p (digitJoin (v, c) (fromDigits acc.reverse)).1
          (digitJoin (v, c) (fromDigits acc.reverse)).2 h
        = ⟨digitJoin (v, c) (fromDigits (digitList start p acc h).value.reverse),
           (digitList start p acc h).pos, (digitList start p acc h).notLonger⟩ := by
  intro p acc h
  fun_induction digitList start p acc h with
  | case1 p acc h c' q hc hd ih =>
    have hkey : digitJoin (v, c) (fromDigits (Spec.digitVal c' :: acc).reverse)
        = digitStep (digitJoin (v, c) (fromDigits acc.reverse)) (Spec.digitVal c') := by
      rw [List.reverse_cons, fromDigits_eq, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ← fromDigits_eq, digitStep_eq, digitStep_eq, digitJoin_assoc]
    rw [digits_go_step hc hd _ _ (by have := step?_lt hc; omega),
      show (digitJoin (v, c) (fromDigits acc.reverse)).1 * 10 + Spec.digitVal c'
          = (digitJoin (v, c) (fromDigits (Spec.digitVal c' :: acc).reverse)).1 from by
        rw [hkey]; simp [digitStep],
      show (digitJoin (v, c) (fromDigits acc.reverse)).2 + 1
          = (digitJoin (v, c) (fromDigits (Spec.digitVal c' :: acc).reverse)).2 from by
        rw [hkey]; simp [digitStep]]
    exact ih
  | case2 p acc h c' q hc hd =>
    refine digits_go_stop _ _ h ?_
    intro c₂ q₂ hcq
    rw [hc] at hcq
    injection hcq with hcq'
    injection hcq' with hcc _
    rw [← hcc]
    simpa using hd
  | case3 p acc h hc =>
    refine digits_go_stop _ _ h ?_
    intro c₂ q₂ hcq
    rw [hc] at hcq
    exact absurd hcq (by simp)

/--
The two digit readers agree from a fresh start, which is the instance that matters: it is what
lets the fast one replace the one every proof about numbers is written against. `digitsFast` is
where reading a long number stopped costing time quadratic in its digits.

`digitsFast start value count` collects the digits into a list and reads them by repeated halving;
`digits start value count` folds them one at a time. Equality is of the whole `Consumed` record,
so the value, the digit count and the stopping position all agree, and the two are interchangeable
wherever either appears. It is `digits_go_eq` at the empty accumulator, where
`digitJoin (value, count) (fromDigits [])` collapses to `(value, count)`.
-/
theorem digitsFast_eq (start : s.Pos) (value count : Nat) :
    digitsFast start value count = digits start value count := by
  have hgo := digits_go_eq start value count start [] (Nat.le_refl _)
  rw [show digitJoin (value, count) (fromDigits ([] : List Nat).reverse) = (value, count) from by
    simp [digitJoin, fromDigits]] at hgo
  rw [digits, digitsFast]
  exact hgo.symm

/--
The compiler is told to run the fast reader in place of the one the library is stated in terms of.
Everything proved about numbers speaks of `digits`, and everything executed is `digitsFast`, and
this is what makes those the same program rather than two that happen to be proved equal.

The equation `@digits = @digitsFast` is between the functions themselves, over every string,
starting position, value and count, which is what `@[csimp]` requires before it will substitute
one for the other in compiled code. It follows from `digitsFast_eq` by `funext`.
-/
@[csimp] theorem digits_eq_digitsFast : @digits = @digitsFast := by
  funext s start value count
  exact (digitsFast_eq start value count).symm


/-- `int = zero / ( digit1-9 *DIGIT )`. A leading zero stands alone, so `01` is two tokens. -/
def intPart (p : s.Pos) : Except Error (Scanned (Nat × Nat) p) :=
  match hc : step? p with
  | some ('0', q) => .ok ⟨(0, 1), q, step?_lt hc⟩
  | some (c, q) =>
    if Spec.isDigit c then
      let r := digits q (Spec.digitVal c) 1
      .ok ⟨r.value, r.pos, by have := r.notLonger; have := step?_lt hc; omega⟩
    else
      .error ⟨byteOffset p, .expectedDigit⟩
  | none => .error ⟨byteOffset p, .expectedDigit⟩

/-- `frac = decimal-point 1*DIGIT`, optional. -/
def fracPart (p : s.Pos) : Except Error (Consumed (Nat × Nat) p) :=
  match hc : step? p with
  | some ('.', q) =>
    match hd : step? q with
    | some (c, r) =>
      if Spec.isDigit c then
        let t := digits r (Spec.digitVal c) 1
        .ok ⟨t.value, t.pos, by
          have := t.notLonger; have := step?_lt hc; have := step?_lt hd; omega⟩
      else
        .error ⟨byteOffset q, .expectedDigit⟩
    | none => .error ⟨byteOffset q, .expectedDigit⟩
  | _ => .ok ⟨(0, 0), p, Nat.le_refl _⟩

/-- An optional `+` or `-`, reporting whether it was a minus. -/
def expSign (p : s.Pos) : Consumed Bool p :=
  match hs : step? p with
  | some ('+', q) => ⟨false, q, Nat.le_of_lt (step?_lt hs)⟩
  | some ('-', q) => ⟨true, q, Nat.le_of_lt (step?_lt hs)⟩
  | _ => ⟨false, p, Nat.le_refl _⟩

/-- `exp = e [ minus / plus ] 1*DIGIT`, optional. -/
def expPart (p : s.Pos) : Except Error (Consumed (Int × Nat) p) :=
  match he : step? p with
  | some (e, q) =>
    if e == 'e' || e == 'E' then
      match expSign q with
      | ⟨negative, r, hsign⟩ =>
        match hd : step? r with
        | some (c, t) =>
          if Spec.isDigit c then
            let u := digits t (Spec.digitVal c) 1
            .ok ⟨(if negative then -(u.value.1 : Int) else (u.value.1 : Int), u.value.2), u.pos, by
              have := u.notLonger; have := step?_lt he; have := step?_lt hd; omega⟩
          else
            .error ⟨byteOffset r, .expectedDigit⟩
        | none => .error ⟨byteOffset r, .expectedDigit⟩
    else
      .ok ⟨(0, 0), p, Nat.le_refl _⟩
  | none => .ok ⟨(0, 0), p, Nat.le_refl _⟩

def tooManyDigits (cfg : Config) (n : Nat) : Bool :=
  match cfg.maxNumberDigits with
  | some limit => limit < n
  | none => false

/--
`number = [ minus ] int [ frac ] [ exp ]`.

The exponent is recorded, never applied, so `1e1000000000` costs no more than a short number.
What is bounded is the count of digits, because a mantissa is built from them one at a time.
-/
def unsignedNumber (cfg : Config) (p : s.Pos) (neg : Bool) : Except Error (Scanned Number p) :=
  match intPart p with
  | .error e => .error e
  | .ok i =>
    match fracPart i.pos with
    | .error e => .error e
    | .ok f =>
      match expPart f.pos with
      | .error e => .error e
      | .ok x =>
        if tooManyDigits cfg (i.value.2 + f.value.2) || tooManyDigits cfg x.value.2 then
          .error ⟨byteOffset p, .tooManyDigits⟩
        else
          let magnitude : Nat := i.value.1 * 10 ^ f.value.2 + f.value.1
          let mantissa : Int := if neg then -(magnitude : Int) else (magnitude : Int)
          .ok ⟨Number.normalize mantissa (x.value.1 - (f.value.2 : Int)), x.pos, by
            have := i.consumed
            have := f.notLonger
            have := x.notLonger
            omega⟩

def number (cfg : Config) (p : s.Pos) : Except Error (Scanned Number p) :=
  match hc : step? p with
  | some ('-', q) =>
    match unsignedNumber cfg q true with
    | .error e => .error e
    | .ok r => .ok ⟨r.value, r.pos, by have := r.consumed; have := step?_lt hc; omega⟩
  | some _ => unsignedNumber cfg p false
  | none => .error ⟨byteOffset p, .unexpectedEnd⟩

/-! ## The machine -/

/--
What remains to be filled in once the value being read is complete. Holding these on the heap is
what keeps nesting off the C stack, so depth costs memory rather than risking a crash.
-/
inductive Frame where
  | arr (elems : Array Json)
  | obj (fields : Array (String × Json)) (seen : Std.HashSet String) (name : String)

def depthExceeded (cfg : Config) (depth : Nat) : Bool :=
  match cfg.maxDepth with
  | some limit => limit ≤ depth
  | none => false

mutual

/-- Read one value, then hand it to the enclosing frames. -/
def value (cfg : Config) (p : s.Pos) (depth : Nat) (stack : List Frame) :
    Except Error (Json × s.Pos) :=
  match _hc : step? p with
  | none => .error ⟨byteOffset p, .unexpectedEnd⟩
  | some ('n', q) =>
    match expect? q ['u', 'l', 'l'] with
    | some ⟨_, r, _hr⟩ => continueWith cfg .null r depth stack
    | none => .error ⟨byteOffset p, .unexpectedChar 'n'⟩
  | some ('t', q) =>
    match expect? q ['r', 'u', 'e'] with
    | some ⟨_, r, _hr⟩ => continueWith cfg (.bool true) r depth stack
    | none => .error ⟨byteOffset p, .unexpectedChar 't'⟩
  | some ('f', q) =>
    match expect? q ['a', 'l', 's', 'e'] with
    | some ⟨_, r, _hr⟩ => continueWith cfg (.bool false) r depth stack
    | none => .error ⟨byteOffset p, .unexpectedChar 'f'⟩
  | some ('"', q) =>
    match string q "" with
    | .error e => .error e
    | .ok ⟨text, r, _hr⟩ => continueWith cfg (.str text) r depth stack
  | some ('[', q) =>
    if depthExceeded cfg depth then .error ⟨byteOffset p, .depthExceeded⟩
    else
      match skipWs q with
      | ⟨_, w, _hw⟩ =>
        match _hb : step? w with
        | some (']', after) => continueWith cfg (.arr #[]) after depth stack
        | _ => value cfg w (depth + 1) (.arr #[] :: stack)
  | some ('{', q) =>
    if depthExceeded cfg depth then .error ⟨byteOffset p, .depthExceeded⟩
    else
      match skipWs q with
      | ⟨_, w, _hw⟩ =>
        match _hb : step? w with
        | some ('}', after) => continueWith cfg (.obj #[]) after depth stack
        | _ => member cfg w (depth + 1) #[] ∅ stack
  | some (c, _) =>
    if c == '-' || Spec.isDigit c then
      match number cfg p with
      | .error e => .error e
      | .ok ⟨n, r, _hr⟩ => continueWith cfg (.num n) r depth stack
    else
      .error ⟨byteOffset p, .unexpectedChar c⟩
termination_by p.remainingBytes
decreasing_by
  all_goals
    first
      | omega
      | (have := step?_lt _hc; omega)
      | (have := step?_lt _hc; have := step?_lt _hb; omega)

/-- A value has just been completed; give it to the innermost frame. -/
def continueWith (cfg : Config) (v : Json) (p : s.Pos) (depth : Nat) (stack : List Frame) :
    Except Error (Json × s.Pos) :=
  match stack with
  | [] => .ok (v, p)
  | .arr elems :: outer =>
    match skipWs p with
    | ⟨_, w, _hw⟩ =>
      match _hb : step? w with
      | some (',', after) =>
        match skipWs after with
        | ⟨_, w₂, _hw₂⟩ => value cfg w₂ depth (.arr (elems.push v) :: outer)
      | some (']', after) => continueWith cfg (.arr (elems.push v)) after (depth - 1) outer
      | some (c, _) => .error ⟨byteOffset w, .unexpectedChar c⟩
      | none => .error ⟨byteOffset w, .unexpectedEnd⟩
  | .obj fields seen name :: outer =>
    match skipWs p with
    | ⟨_, w, _hw⟩ =>
      match _hb : step? w with
      | some (',', after) =>
        match skipWs after with
        | ⟨_, w₂, _hw₂⟩ => member cfg w₂ depth (fields.push (name, v)) seen outer
      | some ('}', after) =>
        continueWith cfg (.obj (fields.push (name, v))) after (depth - 1) outer
      | some (c, _) => .error ⟨byteOffset w, .unexpectedChar c⟩
      | none => .error ⟨byteOffset w, .unexpectedEnd⟩
termination_by p.remainingBytes
decreasing_by all_goals (have := step?_lt _hb; omega)

/-- Having just seen `{` or `,` inside an object, read a member's name and its colon. -/
def member (cfg : Config) (p : s.Pos) (depth : Nat) (fields : Array (String × Json))
    (seen : Std.HashSet String) (stack : List Frame) : Except Error (Json × s.Pos) :=
  match _hc : step? p with
  | some ('"', q) =>
    match string q "" with
    | .error e => .error e
    | .ok ⟨name, k, _hk⟩ =>
      if cfg.duplicateKeys == .reject && seen.contains name then
        .error ⟨byteOffset p, .duplicateKey name⟩
      else
        match skipWs k with
        | ⟨_, w, _hw⟩ =>
          match _hb : step? w with
          | some (':', after) =>
            match skipWs after with
            | ⟨_, w₂, _hw₂⟩ => value cfg w₂ depth (.obj fields (seen.insert name) name :: stack)
          | some (c, _) => .error ⟨byteOffset w, .unexpectedChar c⟩
          | none => .error ⟨byteOffset w, .unexpectedEnd⟩
  | some (c, _) => .error ⟨byteOffset p, .unexpectedChar c⟩
  | none => .error ⟨byteOffset p, .unexpectedEnd⟩
termination_by p.remainingBytes
decreasing_by all_goals (have := step?_lt _hc; have := step?_lt _hb; omega)

end

/-! ## Entry points -/

/-- One complete value read from `start`, and nothing after it but whitespace. -/
def parseFrom (cfg : Config) (start : s.Pos) : Except Error Json :=
  let w := skipWs start
  match value cfg w.pos 0 [] with
  | .error e => .error e
  | .ok (j, p) =>
    let w₂ := skipWs p
    match step? w₂.pos with
    | none => .ok j
    | some (c, _) => .error ⟨byteOffset w₂.pos, .trailingText c⟩

end

/-- Parse JSON text. Text that is not a single complete value is an error, never a partial value. -/
def parse (s : String) (cfg : Config := {}) : Except Error Json :=
  let start :=
    match step? s.startPos with
    | some (c, q) => if cfg.ignoreBOM && c.toNat == 0xFEFF then q else s.startPos
    | none => s.startPos
  parseFrom cfg start

/--
Parse JSON text from bytes. RFC 8259 section 8.1 requires UTF-8, and that is enforced here by the
verified decoder in `Init.Data.String.Decode`.
-/
def parseBytes (b : ByteArray) (cfg : Config := {}) : Except Error Json :=
  match String.fromUTF8? b with
  | some s => parse s cfg
  | none => .error ⟨0, .invalidUtf8⟩

end

end Parser

@[expose] section

@[inherit_doc Parser.parse]
def parse (s : String) (cfg : Config := {}) : Except Error Json := Parser.parse s cfg

@[inherit_doc Parser.parseBytes]
def parseBytes (b : ByteArray) (cfg : Config := {}) : Except Error Json := Parser.parseBytes b cfg

end

end Json
