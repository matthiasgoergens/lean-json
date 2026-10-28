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

/-! ## Scanning a byte at a time -/

/-!
The unescaped characters of a string come in runs, and decoding each character of a run only to
learn that the run goes on is wasted work. `scanWhile` finds where a run ends, and `scanBytes` finds
the same place a byte at a time without decoding anything. That rests on how UTF-8 is built: a
character of one byte is its own code point, below `0x80`, and every byte of a longer character is
at least `0x80`. A byte test that agrees with the character test below `0x80`, and answers for every
byte from `0x80` up what the character test answers for every character beyond ASCII, therefore
stops at the same character boundary.
-/

/--
What `step?` found, in the terms of the `String` library: the position is not the end, the
character is the one there and the next position is the one after it. Lemmas about slices and
bytes of a string are stated in those terms, so this is how a step of the scanner reaches them.

`h : step? p = some (c, q)` says `step?` found `c` at `p` and moved to `q`. The conclusion
supplies `hp : p ≠ s.endPos` together with `p.get hp = c` and `p.next hp = q`. `step?` answers
`some` only in its branch that has such an `hp`, and there it returns exactly that pair.
-/
private theorem step?_eq_some {p q : s.Pos} {c : Char} (h : step? p = some (c, q)) :
    ∃ hp : p ≠ s.endPos, p.get hp = c ∧ p.next hp = q := by
  rw [step?] at h
  split at h
  · simp at h
  · next hp =>
    rw [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hp, h.1, h.2⟩

/-- Where the run of characters satisfying `f` that starts at `p` ends. -/
def scanWhile (f : Char → Bool) (p : s.Pos) : s.Pos :=
  match _hc : step? p with
  | some (c, q) => if f c then scanWhile f q else p
  | none => p
termination_by p.remainingBytes
decreasing_by exact step?_lt _hc

/--
A run ends at or after where it starts. A slice of the text needs its start no later than its
end, and a loop that skips a run needs the run's end to leave no more text than its start did;
both come from this.

`p ≤ scanWhile f p` compares positions in the text, so it says the end of the run of characters
satisfying `f` from `p` lies at `p` or further on. The induction follows `scanWhile`: a run that
stops at once ends at `p` itself, and one that continues ends where the run from the next
character does, which is past `p` by `String.Pos.lt_next`.
-/
private theorem le_scanWhile (f : Char → Bool) (p : s.Pos) : p ≤ scanWhile f p := by
  fun_induction scanWhile f p with
  | case1 p c q hc hf ih =>
    obtain ⟨hp, -, rfl⟩ := step?_eq_some hc
    exact String.Pos.le_of_lt (String.Pos.lt_of_lt_of_le String.Pos.lt_next ih)
  | case2 => exact String.Pos.le_refl _
  | case3 => exact String.Pos.le_refl _

/--
Skipping a run never leaves more text than there was, which is the form the loops' termination
arguments and the scanners' records take.

`(scanWhile f p).remainingBytes ≤ p.remainingBytes` says the bytes left after the run are at most
the bytes left at its start. It is `le_scanWhile` read through
`String.Pos.le_iff_remainingBytes_le`, which turns the order on positions into the reverse order
on what remains.
-/
theorem scanWhile_le (f : Char → Bool) (p : s.Pos) :
    (scanWhile f p).remainingBytes ≤ p.remainingBytes :=
  (String.Pos.le_iff_remainingBytes_le _ _).mp (le_scanWhile f p)

/--
A run that continues past its first character ends where the run from the next character ends.
This is the unfolding of `scanWhile` that a loop taking one character at a time is compared with.

`hc` says `c` is the character at `p` and `q` the position after it, and `hf` says `c` satisfies
`f`. The equation `scanWhile f p = scanWhile f q` holds because `scanWhile` takes its continuing
branch at `p`, whose result is by definition the run from `q`.
-/
private theorem scanWhile_step {f : Char → Bool} {p q : s.Pos} {c : Char}
    (hc : step? p = some (c, q)) (hf : f c = true) : scanWhile f p = scanWhile f q := by
  rw [scanWhile]
  split
  · next c' q' hc' =>
    rw [hc] at hc'
    injection hc' with hc''
    injection hc'' with h₁ h₂
    subst h₁
    subst h₂
    rw [ite_eq_left hf]
  · next hc' => rw [hc] at hc'; exact absurd hc' (by simp)

/-- The byte offset at which a run of bytes satisfying `g`, having reached byte `i`, ends. -/
@[specialize]
def scanBytes (s : String) (g : UInt8 → Bool) (i : Nat) : Nat :=
  if h : i < s.utf8ByteSize then
    if g (s.getUTF8Byte ⟨i⟩ h) then scanBytes s g (i + 1) else i
  else i
termination_by s.utf8ByteSize - i

/--
The bytes of the text at a position are the UTF-8 encoding of the character there. This is what
connects the byte scan, which looks at `s.toByteArray`, to `step?`, which decodes characters.

`hp` says `p` is not the end, so `p.get hp` is a character, and `hk` picks one of its
`utf8Size` bytes. The equation says the byte `k` places after `p` is byte `k` of
`String.utf8EncodeChar (p.get hp)`. It is `String.Pos.utf8Encode_get_eq_extract`, which states
the encoding of the character as a slice of the text's bytes, read at index `k`.
-/
private theorem byte_get {p : s.Pos} (hp : p ≠ s.endPos) {k : Nat}
    (hk : k < (p.get hp).utf8Size) (h : p.offset.byteIdx + k < s.toByteArray.size) :
    s.toByteArray[p.offset.byteIdx + k] =
      (String.utf8EncodeChar (p.get hp))[k]'(by simpa using hk) := by
  have e := p.utf8Encode_get_eq_extract hp
  rw [← ByteArray.getElem_extract (stop := p.offset.byteIdx + (p.get hp).utf8Size)
    (by rw [← e, List.utf8Encode_singleton]; simpa using hk)]
  simp only [← e, List.utf8Encode_singleton, List.getElem_toByteArray]

/--
Every byte of a character UTF-8 spells with more than one byte is at least `0x80`, so no byte
inside such a character can be mistaken for an ASCII character.

`hc` says `c` takes more than one byte, and `k` indexes one of the bytes of
`String.utf8EncodeChar c`. The conclusion is that byte is at least `0x80`. The library spells out
the encoding for each length; every byte in it is some value ored with `0x80`, `0xC0`, `0xE0` or
`0xF0`, each at least `0x80`, and oring cannot make a byte smaller.
-/
private theorem utf8EncodeChar_ge {c : Char} (hc : c.utf8Size ≠ 1) (k : Nat)
    (hk : k < (String.utf8EncodeChar c).length) : 0x80 ≤ (String.utf8EncodeChar c)[k] := by
  have h80 : ∀ m x : UInt8, 0x80 ≤ m → 0x80 ≤ x ||| m := fun m x hm =>
    UInt8.le_trans hm (by rw [UInt8.le_iff_toNat_le, UInt8.toNat_or]; exact Nat.right_le_or)
  have hk' : k < c.utf8Size := by simpa using hk
  rcases c.utf8Size_eq with h | h | h | h
  · exact absurd h hc
  · simp only [String.utf8EncodeChar_eq_cons_cons h]
    rcases k with _ | _ | k
    · exact h80 _ _ (by decide)
    · exact h80 _ _ (by decide)
    · omega
  · simp only [String.utf8EncodeChar_eq_cons_cons_cons h]
    rcases k with _ | _ | _ | k
    · exact h80 _ _ (by decide)
    · exact h80 _ _ (by decide)
    · exact h80 _ _ (by decide)
    · omega
  · simp only [String.utf8EncodeChar_eq_cons_cons_cons_cons h]
    rcases k with _ | _ | _ | _ | k
    · exact h80 _ _ (by decide)
    · exact h80 _ _ (by decide)
    · exact h80 _ _ (by decide)
    · exact h80 _ _ (by decide)
    · omega

/--
The byte scan passes over any stretch of bytes that all satisfy its test, so the proof can step
over a whole character at once while the code takes a byte at a time.

`n` bytes from offset `i` lie within the text by the first hypothesis, and the second says each
of them satisfies `g`. The equation says the scan from `i` ends where the scan from `i + n` does.
The induction is on `n`: each byte passed is one turn of `scanBytes`.
-/
private theorem scanBytes_skip (s : String) (g : UInt8 → Bool) :
    ∀ (n i : Nat), i + n ≤ s.utf8ByteSize →
      (∀ k (h : i + k < s.toByteArray.size), k < n → g s.toByteArray[i + k] = true) →
      scanBytes s g i = scanBytes s g (i + n)
  | 0, i, _, _ => rfl
  | n + 1, i, hn, hb => by
    have hi : i < s.utf8ByteSize := by omega
    rw [scanBytes, dite_eq_left hi, ite_eq_left (by
        rw [String.getUTF8Byte_eq_getElem]; simpa using hb 0 (by simpa using hi) (by omega)),
      scanBytes_skip s g n (i + 1) (by omega) (fun k h hk => by
        have := hb (k + 1) (by simp only [String.size_toByteArray]; omega) (by omega)
        simpa only [show i + (k + 1) = i + 1 + k by omega] using this),
      show i + 1 + n = i + (n + 1) by omega]

/--
The byte scan ends a run exactly where the character scan does, for any pair of tests related as
UTF-8 allows. This is the one fact about UTF-8 the parser relies on beyond what the `String`
library provides.

`h₁` says that on a character of one byte, whose byte is `c.val.toUInt8`, the byte test `g`
answers what the character test `f` answers; `h₂` says that on every byte from `0x80` up `g`
answers what `f` answers on any character of more than one byte. The equation says
`scanBytes s g`, started at the byte offset of `p`, ends at the byte offset of `scanWhile f p`.
The induction follows `scanWhile`. A character that continues the run is passed over by
`scanBytes_skip`, each of its bytes satisfying `g` by `h₁` if it is one byte and by `h₂` with
`utf8EncodeChar_ge` otherwise. At a character that ends the run, its first byte fails `g` by the
same two cases. At the end of the text both stop.
-/
private theorem scanBytes_eq (g : UInt8 → Bool) (f : Char → Bool)
    (h₁ : ∀ c : Char, c.utf8Size = 1 → g c.val.toUInt8 = f c)
    (h₂ : ∀ c : Char, c.utf8Size ≠ 1 → ∀ b : UInt8, 0x80 ≤ b → g b = f c) (p : s.Pos) :
    scanBytes s g p.offset.byteIdx = (scanWhile f p).offset.byteIdx := by
  fun_induction scanWhile f p with
  | case1 p c q hc hf ih =>
    obtain ⟨hp, rfl, rfl⟩ := step?_eq_some hc
    rw [← ih, String.Pos.byteIdx_offset_next]
    apply scanBytes_skip s g
    · have := String.Pos.offset_byteIdx_le_utf8ByteSize s (p.next hp)
      rw [String.Pos.byteIdx_offset_next] at this
      exact this
    · intro k h hk
      rw [byte_get hp hk h]
      by_cases h1 : (p.get hp).utf8Size = 1
      · obtain rfl : k = 0 := by omega
        simp only [String.utf8EncodeChar_eq_singleton h1, List.getElem_cons_zero]
        rw [h₁ _ h1]
        exact hf
      · rw [h₂ _ h1 _ (utf8EncodeChar_ge h1 k _)]
        exact hf
  | case2 p c q hc hf =>
    obtain ⟨hp, rfl, rfl⟩ := step?_eq_some hc
    have hlt : p.offset.byteIdx < s.utf8ByteSize := by
      have := String.Pos.offset_byteIdx_le_utf8ByteSize s (p.next hp)
      rw [String.Pos.byteIdx_offset_next] at this
      have := Char.utf8Size_pos (p.get hp)
      omega
    rw [scanBytes, dite_eq_left hlt, ite_eq_right]
    have hb := byte_get hp (k := 0) (Char.utf8Size_pos _) (by simpa using hlt)
    simp only [Nat.add_zero] at hb
    rw [String.getUTF8Byte_eq_getElem, hb]
    by_cases h1 : (p.get hp).utf8Size = 1
    · simp only [String.utf8EncodeChar_eq_singleton h1, List.getElem_cons_zero]
      rw [h₁ _ h1]
      simpa using hf
    · rw [h₂ _ h1 _ (utf8EncodeChar_ge h1 0 _)]
      simpa using hf
  | case3 p hc =>
    have hp : p = s.endPos := by
      rw [step?] at hc
      split at hc
      · assumption
      · simp at hc
    subst hp
    rw [scanBytes, dite_eq_right (by simp)]

/--
`scanWhile f`, computed by the byte scan `scanBytes s g`. The proof that the byte offset it
reaches is a character boundary is `scanBytes_eq`, which is why `h₁` and `h₂` are arguments.
-/
@[inline]
def scanBytesPos (g : UInt8 → Bool) (f : Char → Bool)
    (h₁ : ∀ c : Char, c.utf8Size = 1 → g c.val.toUInt8 = f c)
    (h₂ : ∀ c : Char, c.utf8Size ≠ 1 → ∀ b : UInt8, 0x80 ≤ b → g b = f c) (p : s.Pos) : s.Pos :=
  ⟨⟨scanBytes s g p.offset.byteIdx⟩, by
    rw [scanBytes_eq g f h₁ h₂]; exact (scanWhile f p).isValid⟩

/--
The position the byte scan reaches is the end of the run. This is the form the `csimp` lemmas
below need, an equation between positions rather than byte offsets.

`scanBytesPos g f h₁ h₂ p` is the position at the byte offset `scanBytes` reaches, and
`scanWhile f p` is the end of the run of characters satisfying `f`. Two positions are equal when
their byte offsets are, and `scanBytes_eq` says these agree.
-/
private theorem scanBytesPos_eq (g : UInt8 → Bool) (f : Char → Bool)
    (h₁ : ∀ c : Char, c.utf8Size = 1 → g c.val.toUInt8 = f c)
    (h₂ : ∀ c : Char, c.utf8Size ≠ 1 → ∀ b : UInt8, 0x80 ≤ b → g b = f c) (p : s.Pos) :
    scanBytesPos g f h₁ h₂ p = scanWhile f p :=
  String.Pos.ext (String.Pos.Raw.ext (scanBytes_eq g f h₁ h₂ p))

/--
A character of one byte has that byte's value as its code point. Each byte test below is checked
against its character test through this.

`hc` says `c` takes one byte, which `Char.utf8Size_eq_one_iff` turns into `c.val ≤ 127`. The
equation says the byte `c.val.toUInt8`, read as a number, is `c.toNat`; truncating to eight bits
loses nothing below `0x80`.
-/
private theorem toNat_toUInt8 {c : Char} (hc : c.utf8Size = 1) :
    c.val.toUInt8.toNat = c.toNat ∧ c.toNat < 0x80 := by
  have h127 : c.toNat ≤ 127 := by
    simpa [UInt32.le_iff_toNat_le] using Char.utf8Size_eq_one_iff.mp hc
  refine ⟨?_, by omega⟩
  rw [UInt32.toNat_toUInt8]
  exact Nat.mod_eq_of_lt (show c.toNat < 2 ^ 8 by omega)

/--
A character of more than one byte is beyond ASCII, which is what decides both character tests
for it.

`hc` says `c` does not take one byte, so by `Char.utf8Size_eq_one_iff` its code point is above
`127`, and `0x80 ≤ c.toNat` says exactly that.
-/
private theorem toNat_ge_of_utf8Size {c : Char} (hc : c.utf8Size ≠ 1) : 0x80 ≤ c.toNat := by
  have : ¬ c.val ≤ 127 := fun h => hc (Char.utf8Size_eq_one_iff.mpr h)
  simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at this
  show 0x80 ≤ c.val.toNat
  omega

/-! ## Strings a run at a time -/

/-!
`string` appends one character at a time, which in compiled code is an allocation and a push for
each one. A run of unescaped characters stands for itself, so `stringFast` copies each run whole
and goes through `stringStep` only where a run ends. The two are proved equal, so `string` is
what the proofs speak of and `stringFast` is what runs.
-/

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

/-- Where the run of unescaped characters that starts at `p` ends. -/
def unescapedEnd (p : s.Pos) : s.Pos := scanWhile Spec.isUnescaped p

/-- A byte that cannot end a run of unescaped characters. -/
@[inline]
def continuesRun (b : UInt8) : Bool := 0x20 ≤ b && b != 0x22 && b != 0x5C

/--
For a character of one byte, the byte test for continuing a run and the grammar's test for an
unescaped character agree, which is the first condition `scanBytes_eq` asks of a byte test.

`hc` says `c` takes one byte, so `c.val.toUInt8` is that byte and has the value `c.toNat`, below
`0x80`. `continuesRun` asks for at least `0x20` and neither `0x22` nor `0x5C`;
`Spec.isUnescaped c` asks for `0x20` to `0x21`, `0x23` to `0x5B`, or at least `0x5D`. Below
`0x80` those are the same numbers.
-/
theorem continuesRun_ascii (c : Char) (hc : c.utf8Size = 1) :
    continuesRun c.val.toUInt8 = Spec.isUnescaped c := by
  have hn : c.toUInt8.toNat = c.toNat := (toNat_toUInt8 hc).1
  rw [Bool.eq_iff_iff]
  simp [continuesRun, Spec.isUnescaped, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, hn]
  omega

/--
Every byte from `0x80` up continues a run, and every character beyond ASCII is unescaped, which
is the second condition `scanBytes_eq` asks of a byte test.

`hc` says `c` takes more than one byte, so its code point is at least `0x80` and above `0x5D`, and
`hb` says the byte `b` is at least `0x80`, so neither below `0x20` nor `0x22` nor `0x5C`. Both
tests answer `true`.
-/
theorem continuesRun_high (c : Char) (hc : c.utf8Size ≠ 1) (b : UInt8) (hb : 0x80 ≤ b) :
    continuesRun b = Spec.isUnescaped c := by
  have hn := toNat_ge_of_utf8Size hc
  simp only [UInt8.le_iff_toNat_le, UInt8.reduceToNat] at hb
  rw [Bool.eq_iff_iff]
  simp [continuesRun, Spec.isUnescaped, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj]
  omega

def unescapedEndFast (p : s.Pos) : s.Pos :=
  scanBytesPos continuesRun Spec.isUnescaped continuesRun_ascii continuesRun_high p

/--
The compiler is told to find the end of a run of unescaped characters a byte at a time.
`stringFast` is written with `unescapedEnd`, and so is every proof about it; this makes what runs
the byte scan.

The equation `@unescapedEnd = @unescapedEndFast` is between the functions, over every text and
position, as `@[csimp]` requires. `unescapedEndFast` is `scanBytesPos` with the tests for
unescaped characters, which `scanBytesPos_eq` equates with `scanWhile Spec.isUnescaped`, the
definition of `unescapedEnd`.
-/
@[csimp] theorem unescapedEnd_eq_unescapedEndFast : @unescapedEnd = @unescapedEndFast := by
  funext s p
  exact (scanBytesPos_eq _ _ _ _ p).symm

/-- `acc` followed by the text from `p` to `q`, which is that text itself when `acc` is empty. -/
def appendRun (acc : String) (p q : s.Pos) : String :=
  if acc.isEmpty then s.extract p q else acc ++ s.extract p q

/--
Leaving out the empty accumulator changes nothing. It saves a copy on the commonest string of
all, one with no escape, whose whole content is a single run appended to `""`.

`appendRun acc p q` is the text from `p` to `q` when `acc` is empty and `acc` followed by it
otherwise; `acc ++ s.extract p q` is the latter in every case. The two agree because `"" ++ t` is
`t`.
-/
private theorem appendRun_eq (acc : String) (p q : s.Pos) :
    appendRun acc p q = acc ++ s.extract p q := by
  unfold appendRun
  split
  · next h => rw [String.isEmpty_iff.mp h, String.empty_append]
  · rfl

/--
Pushing a run's first character and then copying the rest of the run is copying the whole run.
This is the step that lets one copy stand for a push per character.

`hc` says `c` is the character at `p` and `q` the position after it, and `hq` says the run's end
`e` is not before `q`. The equation says `acc.push c` followed by the text from `q` to `e` is
`acc` followed by the text from `p` to `e`. `String.copy_slice_eq_append_of_lt` splits the latter
text into its first character and the rest, and `String.append_singleton` identifies appending
that character with pushing it.
-/
private theorem push_append_extract {p q e : s.Pos} {c : Char} (hc : step? p = some (c, q))
    (hq : q ≤ e) (acc : String) : acc.push c ++ s.extract q e = acc ++ s.extract p e := by
  obtain ⟨hp, rfl, rfl⟩ := step?_eq_some hc
  have hlt : p < e := String.Pos.lt_of_lt_of_le String.Pos.lt_next hq
  rw [String.extract_eq_copy_slice _ _ hq,
    String.extract_eq_copy_slice _ _ (String.Pos.le_of_lt hlt),
    String.copy_slice_eq_append_of_lt hlt, ← String.append_singleton, String.append_assoc]

/--
The string loop called at the same position with the same accumulator gives the same result,
whatever proof of its bound it carries. The loop's results are compared at positions computed in
two ways, so they have to be matched up to an equation rather than syntactically.

`hp` and `hacc` say the positions and the accumulators are equal; `h` and `h'` are the bounds
each call carries. Once the equations are substituted, the bounds are proofs of one proposition,
and so are the same.
-/
private theorem string_go_congr {start p p' : s.Pos} {acc acc' : String} (hp : p = p')
    (hacc : acc = acc') (h : p.remainingBytes ≤ start.remainingBytes)
    (h' : p'.remainingBytes ≤ start.remainingBytes) :
    string.go start p acc h = string.go start p' acc' h' := by
  subst hp
  subst hacc
  rfl

/--
One turn of the string loop on an unescaped character pushes it and carries on from the next
position. This is the unfolding of `string.go` that a run is made of, stated as an equation
because the loop's bound argument keeps `rw` from unfolding it in place.

`hc` says `c` is the character at `p` and `q` the position after it, and `hu` says it is
unescaped. The equation relates the loop at `p` with accumulator `acc` to the loop at `q` with
`acc.push c`; `h` and `h'` are their bounds. `stringStep_unescaped` fixes what the loop's one
`stringStep` returns, which rules out its other two branches.
-/
private theorem string_go_unescaped {start p q : s.Pos} {c : Char} (hc : step? p = some (c, q))
    (hu : Spec.isUnescaped c = true) (acc : String) (h : p.remainingBytes ≤ start.remainingBytes)
    (h' : q.remainingBytes ≤ start.remainingBytes) :
    string.go start p acc h = string.go start q (acc.push c) h' := by
  rw [string.go]
  split
  · next e hs => rw [stringStep_unescaped hc hu] at hs; simp at hs
  · next r hs => rw [stringStep_unescaped hc hu] at hs; simp at hs
  · next c' r hs =>
    rw [stringStep_unescaped hc hu] at hs
    injection hs with h₁ h₂
    subst h₁
    subst h₂
    rfl

/--
The string loop passes over a run of unescaped characters as one copy of the run. This is the
whole difference between `string` and `stringFast`, which otherwise take the same steps.

`string.go start p acc h` is the loop at `p` holding `acc`. The equation says it equals the loop
at `scanWhile Spec.isUnescaped p`, the end of the run, holding `acc` followed by the run's text;
`h'` is that call's bound. The induction follows `scanWhile`: where the run stops at once the
text is empty, and where it continues `string_go_unescaped` takes one character and
`push_append_extract` moves it into the copy.
-/
private theorem string_go_run (start p : s.Pos) :
    ∀ (acc : String) (h : p.remainingBytes ≤ start.remainingBytes)
      (h' : (scanWhile Spec.isUnescaped p).remainingBytes ≤ start.remainingBytes),
      string.go start p acc h =
        string.go start (scanWhile Spec.isUnescaped p)
          (acc ++ s.extract p (scanWhile Spec.isUnescaped p)) h' := by
  fun_induction scanWhile Spec.isUnescaped p with
  | case1 p c q hc hu ih =>
    intro acc h h'
    have hq : q.remainingBytes ≤ start.remainingBytes := by have := step?_lt hc; omega
    rw [string_go_unescaped hc hu acc h hq, ih (acc.push c) hq h']
    exact string_go_congr rfl (push_append_extract hc (le_scanWhile _ q) acc) _ _
  | case2 | case3 =>
    intro acc h h'
    rw [String.extract_eq_copy_slice _ _ (String.Pos.le_refl _), String.copy_slice_self,
      String.append_empty]

def stringFast (start : s.Pos) (acc : String) : Except Error (Scanned String start) :=
  go start acc (Nat.le_refl _)
where
  go (p : s.Pos) (acc : String) (h : p.remainingBytes ≤ start.remainingBytes) :
      Except Error (Scanned String start) :=
    match hs : stringStep (unescapedEnd p) with
    | .fail e => .error e
    | .done q =>
      .ok ⟨appendRun acc p (unescapedEnd p), q, by
        have := stringStep_done_lt _ q hs; have : (unescapedEnd p).remainingBytes ≤ p.remainingBytes :=
          scanWhile_le _ p
        omega⟩
    | .char c q =>
      go q ((appendRun acc p (unescapedEnd p)).push c) (by
        have := stringStep_char_lt _ c q hs; have : (unescapedEnd p).remainingBytes ≤ p.remainingBytes :=
          scanWhile_le _ p
        omega)
  termination_by p.remainingBytes
  decreasing_by
    have := stringStep_char_lt _ c q hs
    have : (unescapedEnd p).remainingBytes ≤ p.remainingBytes := scanWhile_le _ p
    omega

/--
The run-copying loop and the character loop agree at every position and accumulator, which is
the form general enough to be an induction hypothesis.

`stringFast.go start p acc h` and `string.go start p acc h` are the two loops at `p` holding
`acc`, with the same bound `h`. The induction follows `stringFast.go`, whose three cases are what
`stringStep` reports at the end of the run. In each, `string_go_run` carries `string.go` to the
same place with the run appended, after which both loops take the same branch; `appendRun_eq`
identifies their accumulators.
-/
private theorem stringFast_go_eq (start p : s.Pos) (acc : String)
    (h : p.remainingBytes ≤ start.remainingBytes) :
    stringFast.go start p acc h = string.go start p acc h := by
  have hrun := fun p acc (h : p.remainingBytes ≤ start.remainingBytes) =>
    string_go_run start p acc h (Nat.le_trans (scanWhile_le _ p) h)
  fun_induction stringFast.go start p acc h with
  | case1 p acc h err hs =>
    rw [hrun, string.go]
    split
    · next e hs' => rw [unescapedEnd] at hs; rw [hs] at hs'; injection hs' with hh; subst hh; rfl
    · next r hs' => rw [unescapedEnd] at hs; rw [hs] at hs'; simp at hs'
    · next c r hs' => rw [unescapedEnd] at hs; rw [hs] at hs'; simp at hs'
  | case2 p acc h q hs =>
    rw [hrun, string.go]
    split
    · next e hs' => rw [unescapedEnd] at hs; rw [hs] at hs'; simp at hs'
    · next r hs' =>
      rw [unescapedEnd] at hs
      rw [hs] at hs'
      injection hs' with hh
      subst hh
      simp only [appendRun_eq, unescapedEnd]
    · next c r hs' => rw [unescapedEnd] at hs; rw [hs] at hs'; simp at hs'
  | case3 p acc h c q hs ih =>
    rw [hrun, string.go]
    split
    · next e hs' => rw [unescapedEnd] at hs; rw [hs] at hs'; simp at hs'
    · next r hs' => rw [unescapedEnd] at hs; rw [hs] at hs'; simp at hs'
    · next c' r hs' =>
      rw [unescapedEnd] at hs
      rw [hs] at hs'
      injection hs' with h₁ h₂
      subst h₁
      subst h₂
      rw [ih]
      exact string_go_congr rfl (by rw [appendRun_eq, unescapedEnd]) _ _

/--
The compiler is told to read strings a run at a time in place of a character at a time.
Everything proved about strings speaks of `string`, everything executed is `stringFast`, and this
is what makes those the same program.

The equation `@string = @stringFast` is between the functions themselves, over every text,
starting position and accumulator, which is what `@[csimp]` requires before it will substitute
one for the other in compiled code. It is `stringFast_go_eq` at the loop's entry, where both
start at `start` with the given accumulator.
-/
@[csimp] theorem string_eq_stringFast : @string = @stringFast := by
  funext s start acc
  exact (stringFast_go_eq start start acc _).symm

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

/-- At most `k` more digits, folded in as `digits.go` folds them. -/
def digitsUpTo (start p : s.Pos) (v n : Nat) (h : p.remainingBytes ≤ start.remainingBytes) :
    Nat → Consumed (Nat × Nat) start
  | 0 => ⟨(v, n), p, h⟩
  | k + 1 =>
    match hc : step? p with
    | some (c, q) =>
      if Spec.isDigit c then
        digitsUpTo start q (v * 10 + Spec.digitVal c) (n + 1) (by have := step?_lt hc; omega) k
      else
        ⟨(v, n), p, h⟩
    | none => ⟨(v, n), p, h⟩

/--
How many digits after the first are read by folding before the rest of a run is handed to the
halving reader. Every number a parse sees starts with one digit already read, so a run of up to
eighteen is folded into a value below `2 ^ 63`, which needs no allocation, and only longer runs
pay for building a list.
-/
def foldedDigits : Nat := 17

def digitsFast (start : s.Pos) (value count : Nat) : Consumed (Nat × Nat) start :=
  let r := digitsUpTo start start value count (Nat.le_refl _) foldedDigits
  if r.value.2 < count + foldedDigits then r
  else
    let l := digitList start r.pos [] r.notLonger
    ⟨digitJoin r.value (fromDigits l.value.reverse), l.pos, l.notLonger⟩

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
Folding up to `k` digits and then carrying on with the loop is the loop: `digitsUpTo` runs the
same steps as `digits.go`, so the loop resumed where it stopped ends where the loop alone would.
-/
private theorem digits_go_upTo (start : s.Pos) :
    ∀ (k : Nat) (p : s.Pos) (v n : Nat) (h : p.remainingBytes ≤ start.remainingBytes),
      digits.go start p v n h =
        digits.go start (digitsUpTo start p v n h k).pos (digitsUpTo start p v n h k).value.1
          (digitsUpTo start p v n h k).value.2 (digitsUpTo start p v n h k).notLonger := by
  intro k
  induction k with
  | zero => intro p v n h; rfl
  | succ k ih =>
    intro p v n h
    rw [digitsUpTo]
    split
    · next c q hc =>
      split
      · next hd =>
        rw [digits_go_step hc hd v n h (by have := step?_lt hc; omega)]
        exact ih _ _ _ _
      · rfl
    · rfl

/--
When `digitsUpTo` returns before using up its `k` digits, it stopped where the digits do: what
follows, if anything, is not a digit, so the loop has nothing more to read there.
-/
private theorem digitsUpTo_stop (start : s.Pos) :
    ∀ (k : Nat) (p : s.Pos) (v n : Nat) (h : p.remainingBytes ≤ start.remainingBytes),
      (digitsUpTo start p v n h k).value.2 < n + k →
      ∀ c q, step? (digitsUpTo start p v n h k).pos = some (c, q) → Spec.isDigit c = false := by
  intro k
  induction k with
  | zero => intro p v n h hlt; simp [digitsUpTo] at hlt
  | succ k ih =>
    intro p v n h
    rw [digitsUpTo]
    split
    · next c' q' hc =>
      split
      · next hd => intro hlt; exact ih _ _ _ _ (by omega)
      · next hd =>
        intro _ c q hcq
        rw [hc] at hcq
        injection hcq with hcq'
        injection hcq' with hcc _
        rw [← hcc]
        simpa using hd
    · next hc =>
      intro _ c q hcq
      rw [hc] at hcq
      exact absurd hcq (by simp)

/--
The two digit readers agree from a fresh start, which is the instance that matters: it is what
lets the fast one replace the one every proof about numbers is written against. `digitsFast` is
where reading a long number stopped costing time quadratic in its digits.

`digitsFast start value count` folds up to `foldedDigits` digits, then collects any that remain
into a list and reads them by repeated halving; `digits start value count` folds them all one at a
time. Equality is of the whole `Consumed` record, so the value, the digit count and the stopping
position all agree, and the two are interchangeable wherever either appears. A run that ends
early is `digits_go_stop` where the folding stopped; a longer one is `digits_go_eq` from there, at
the empty accumulator, where `digitJoin (v, c) (fromDigits [])` collapses to `(v, c)`.
-/
theorem digitsFast_eq (start : s.Pos) (value count : Nat) :
    digitsFast start value count = digits start value count := by
  rw [digits, digits_go_upTo start foldedDigits]
  unfold digitsFast
  simp only
  split
  · next hlt => rw [digits_go_stop _ _ _ (digitsUpTo_stop start foldedDigits _ _ _ _ hlt)]
  · have hgo := digits_go_eq start
      (digitsUpTo start start value count (Nat.le_refl _) foldedDigits).value.1
      (digitsUpTo start start value count (Nat.le_refl _) foldedDigits).value.2
      (digitsUpTo start start value count (Nat.le_refl _) foldedDigits).pos []
      (digitsUpTo start start value count (Nat.le_refl _) foldedDigits).notLonger
    rw [show ∀ v c, digitJoin (v, c) (fromDigits ([] : List Nat).reverse) = (v, c) from by
      simp [digitJoin, fromDigits]] at hgo
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
