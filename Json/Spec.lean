/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Basic

public section

/-!
A transcription of the ABNF in RFC 8259, section 2, meant to be read against the RFC rather than
against the parser.

Each relation carries the text it consumes, the value that text denotes, and the text remaining
after it, so a sequence of productions threads the remainder through. `Text` ties the knot by
requiring the remainder to be empty.

The alphabet is `Char` rather than bytes. The RFC states the string productions in code points,
and section 8.1 requires UTF-8 for interchange, so the byte level belongs to the entry point that
decodes a `ByteArray`, using the verified decoder in `Init.Data.String.Decode`. That leaves this
module at the level the RFC itself is written in.
-/

namespace Json.Spec

@[expose] section

/-! ## Whitespace and structural characters -/

/-- `ws = *( %x20 / %x09 / %x0A / %x0D )` -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0d'

inductive Ws : List Char → List Char → Prop where
  | nil {r} : Ws r r
  | cons {c s r} : isWs c = true → Ws s r → Ws (c :: s) r

/-- A structural character with whitespace either side, as in `begin-array = ws %x5B ws`. -/
inductive Token (t : Char) : List Char → List Char → Prop where
  | mk {s s' r} : Ws s (t :: s') → Ws s' r → Token t s r

abbrev BeginArray := Token '['
abbrev EndArray := Token ']'
abbrev BeginObject := Token '{'
abbrev EndObject := Token '}'
abbrev NameSeparator := Token ':'
abbrev ValueSeparator := Token ','

/-! ## Numbers -/

/-- `DIGIT = %x30-39` -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

def digitVal (c : Char) : Nat := c.toNat - '0'.toNat

/-- `1*DIGIT`, carrying both the value and how many digits produced it. -/
inductive Digits : List Char → Nat → Nat → List Char → Prop where
  | last {c r} : isDigit c = true → Digits (c :: r) (digitVal c) 1 r
  | cons {c s v n r} : isDigit c = true → Digits s v n r →
      Digits (c :: s) (digitVal c * 10 ^ n + v) (n + 1) r

/-- `int = zero / ( digit1-9 *DIGIT )` -/
inductive Int' : List Char → Nat → List Char → Prop where
  | zero {r} : Int' ('0' :: r) 0 r
  | digits {c s v n r} : ('1' ≤ c && c ≤ '9') = true → Digits (c :: s) v n r → Int' (c :: s) v r

/-- `frac = decimal-point 1*DIGIT`, optional. -/
inductive Frac : List Char → Nat → Nat → List Char → Prop where
  | absent {r} : Frac r 0 0 r
  | present {s v n r} : Digits s v n r → Frac ('.' :: s) v n r

/-- `exp = e [ minus / plus ] 1*DIGIT`, optional. -/
inductive Exp : List Char → Int → List Char → Prop where
  | absent {r} : Exp r 0 r
  | bare {c s v n r} : (c = 'e' ∨ c = 'E') → Digits s v n r → Exp (c :: s) (v : Int) r
  | plus {c s v n r} : (c = 'e' ∨ c = 'E') → Digits s v n r → Exp (c :: '+' :: s) (v : Int) r
  | minus {c s v n r} : (c = 'e' ∨ c = 'E') → Digits s v n r → Exp (c :: '-' :: s) (-(v : Int)) r

/-- `minus = %x2D`, optional. -/
inductive Sign : List Char → Bool → List Char → Prop where
  | absent {r} : Sign r false r
  | minus {r} : Sign ('-' :: r) true r

/--
`number = [ minus ] int [ frac ] [ exp ]`.

The digits denote `± (int ++ frac) * 10 ^ (exp - |frac|)`, and the value recorded is that
number's canonical form.
-/
inductive Num : List Char → Number → List Char → Prop where
  | mk {s s₁ s₂ s₃ r neg i f nf e} :
      Sign s neg s₁ → Int' s₁ i s₂ → Frac s₂ f nf s₃ → Exp s₃ e r →
      Num s (Number.normalize
        (if neg then -((i * 10 ^ nf + f : Nat) : Int) else ((i * 10 ^ nf + f : Nat) : Int))
        (e - nf)) r

/-! ## Strings -/

/-- `unescaped = %x20-21 / %x23-5B / %x5D-10FFFF` -/
def isUnescaped (c : Char) : Bool :=
  (0x20 ≤ c.toNat && c.toNat ≤ 0x21) || (0x23 ≤ c.toNat && c.toNat ≤ 0x5B) || 0x5D ≤ c.toNat

/-- `HEXDIG` -/
def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- `4HEXDIG` -/
inductive Hex4 : List Char → Nat → List Char → Prop where
  | mk {c₁ c₂ c₃ c₄ v₁ v₂ v₃ v₄ r} :
      hexVal? c₁ = some v₁ → hexVal? c₂ = some v₂ → hexVal? c₃ = some v₃ →
      hexVal? c₄ = some v₄ →
      Hex4 (c₁ :: c₂ :: c₃ :: c₄ :: r) (v₁ * 4096 + v₂ * 256 + v₃ * 16 + v₄) r

/--
`char = unescaped / escape ( %x22 / %x5C / %x2F / %x62 / %x66 / %x6E / %x72 / %x74 / %x75 4HEXDIG )`

An unpaired surrogate escape relates to no character at all, because no `Char` carries a
surrogate code point. Rejecting them is therefore a consequence of the alphabet rather than a
rule imposed on top of it.
-/
inductive Ch : List Char → Char → List Char → Prop where
  | unescaped {c r} : isUnescaped c = true → Ch (c :: r) c r
  | quote {r} : Ch ('\\' :: '"' :: r) '"' r
  | backslash {r} : Ch ('\\' :: '\\' :: r) '\\' r
  | solidus {r} : Ch ('\\' :: '/' :: r) '/' r
  | backspace {r} : Ch ('\\' :: 'b' :: r) '\x08' r
  | formFeed {r} : Ch ('\\' :: 'f' :: r) '\x0c' r
  | lineFeed {r} : Ch ('\\' :: 'n' :: r) '\n' r
  | carriageReturn {r} : Ch ('\\' :: 'r' :: r) '\x0d' r
  | tab {r} : Ch ('\\' :: 't' :: r) '\t' r
  | codePoint {s v r c} : Hex4 s v r → c.toNat = v → Ch ('\\' :: 'u' :: s) c r
  | surrogatePair {s₁ s₂ hi lo r c} :
      Hex4 s₁ hi ('\\' :: 'u' :: s₂) → Hex4 s₂ lo r →
      0xD800 ≤ hi → hi ≤ 0xDBFF → 0xDC00 ≤ lo → lo ≤ 0xDFFF →
      c.toNat = 0x10000 + (hi - 0xD800) * 0x400 + (lo - 0xDC00) →
      Ch ('\\' :: 'u' :: s₁) c r

/-- `*char` -/
inductive Chars : List Char → List Char → List Char → Prop where
  | nil {r} : Chars r [] r
  | cons {s s' cs c r} : Ch s c s' → Chars s' cs r → Chars s (c :: cs) r

/-- `string = quotation-mark *char quotation-mark` -/
inductive Str : List Char → String → List Char → Prop where
  | mk {s cs r} : Chars s cs ('"' :: r) → Str ('"' :: s) (String.ofList cs) r

/-! ## Values -/

mutual

/-- `value = false / null / true / object / array / number / string` -/
inductive Value : List Char → Json → List Char → Prop where
  | false_ {r} : Value ('f' :: 'a' :: 'l' :: 's' :: 'e' :: r) (.bool false) r
  | null {r} : Value ('n' :: 'u' :: 'l' :: 'l' :: r) .null r
  | true_ {r} : Value ('t' :: 'r' :: 'u' :: 'e' :: r) (.bool true) r
  | obj {s fields r} : Object s fields r → Value s (.obj fields) r
  | arr {s elems r} : Arr s elems r → Value s (.arr elems) r
  | num {s n r} : Num s n r → Value s (.num n) r
  | str {s v r} : Str s v r → Value s (.str v) r

/-- `array = begin-array [ value *( value-separator value ) ] end-array` -/
inductive Arr : List Char → Array Json → List Char → Prop where
  | empty {s s' r} : BeginArray s s' → EndArray s' r → Arr s #[] r
  | items {s s' s'' vs r} : BeginArray s s' → Elements s' vs s'' → EndArray s'' r →
      Arr s vs.toArray r

/-- `value *( value-separator value )`: an array's members, the brackets and the empty case
being `Value`'s. -/
inductive Elements : List Char → List Json → List Char → Prop where
  | one {s v r} : Value s v r → Elements s [v] r
  | more {s s' s'' v vs r} : Value s v s' → ValueSeparator s' s'' → Elements s'' vs r →
      Elements s (v :: vs) r

/-- `object = begin-object [ member *( value-separator member ) ] end-object` -/
inductive Object : List Char → Array (String × Json) → List Char → Prop where
  | empty {s s' r} : BeginObject s s' → EndObject s' r → Object s #[] r
  | members {s s' s'' ms r} : BeginObject s s' → Members s' ms s'' → EndObject s'' r →
      Object s ms.toArray r

/-- `member *( value-separator member )`: an object's members, the braces and the empty case
being `Value`'s. -/
inductive Members : List Char → List (String × Json) → List Char → Prop where
  | one {s m r} : Member s m r → Members s [m] r
  | more {s s' s'' m ms r} : Member s m s' → ValueSeparator s' s'' → Members s'' ms r →
      Members s (m :: ms) r

/-- `member = string name-separator value` -/
inductive Member : List Char → (String × Json) → List Char → Prop where
  | mk {s s' s'' k v r} : Str s k s' → NameSeparator s' s'' → Value s'' v r → Member s (k, v) r

end

/-- `JSON-text = ws value ws` -/
def Text (s : List Char) (j : Json) : Prop :=
  ∃ s₁ s₂, Ws s s₁ ∧ Value s₁ j s₂ ∧ Ws s₂ []

/-- `Text` for a `String`, which is the form the parser's entry point takes. -/
def TextOf (s : String) (j : Json) : Prop := Text s.toList j

/-! ## Inversion

Construction says what the grammar accepts; rejection needs the other direction. `cases`
discharges most alternatives on its own, from the shape of the character list. What it cannot see
is that whitespace never swallows a non-whitespace character, and that no character carries a
surrogate code point, which is where D8 becomes a property of the alphabet rather than a rule
imposed on the grammar.
-/

/--
Whitespace stops at the first character that is not whitespace. Every proof that the grammar
refuses a text begins by pinning down where its leading whitespace ends, and without this `Ws`
could be read as skipping over a `[` or a `,`, leaving no text the grammar demonstrably rejects.

`hc : isWs c = false` says `c` is none of space, tab, line feed or carriage return. Given a
derivation `Ws (c :: s) r`, which says whitespace consumed some prefix of `c :: s` and left `r`,
the conclusion `r = c :: s` says it consumed nothing. `Ws` has two constructors: `nil` gives that
conclusion outright, and `cons`, the one that would consume `c`, requires `isWs c = true` and so
contradicts `hc`.
-/
theorem ws_eq_of_not_isWs {c : Char} {s r : List Char} (hc : isWs c = false) :
    Ws (c :: s) r → r = c :: s := by
  intro h
  cases h with
  | nil => rfl
  | cons hws _ => rw [hc] at hws; exact absurd hws (by decide)

/--
A structural character cannot be found where the text begins with a different character that is
not whitespace. This is the whole of what rejection proofs need about `[`, `]`, `{`, `}`, `:` and
`,`: no derivation can read a `,` where the grammar calls for a `:`.

`hc` says the leading character `c` is not whitespace and `hne` says it is not the token `t` being
sought. `¬ Token t (c :: s) r` denies that any derivation exists, for any remainder `r`.
`Token t` is whitespace, then `t`, then whitespace; `ws_eq_of_not_isWs` says the leading
whitespace consumes nothing, so the `t` would have to be `c` itself, which `hne` forbids.
-/
theorem not_token_of_ne {t c : Char} {s r : List Char} (hc : isWs c = false) (hne : c ≠ t) :
    ¬ Token t (c :: s) r := by
  rintro ⟨hws, -⟩
  have := ws_eq_of_not_isWs hc hws
  simp at this
  exact hne this.1.symm

/--
No `Char` carries a surrogate code point. This is why the grammar can be written over `Char` and
still enforce RFC 8259's rule that an unpaired surrogate escape denotes no character: the rule
falls out of the alphabet rather than being a side condition every production has to repeat.

`c.toNat` is `c`'s code point as a number. `c.toNat < 0xD800 ∨ 0xDFFF < c.toNat` places it below
or above the surrogate block `D800`-`DFFF`, so never inside it. It is read off `Char.valid`, the
invariant carried by every `Char`, so it holds of every character with no exception.
-/
theorem char_not_surrogate (c : Char) : c.toNat < 0xD800 ∨ 0xDFFF < c.toNat := by
  have h := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at h
  simp only [Char.toNat]
  omega

/--
A `\u` escape that names a character names one outside the surrogate block. This is the form in
which the alphabet's guarantee is used: the grammar relates an escape to a character by their
numbers, and this says that number cannot be a surrogate, which leaves the paired rule as the only
way to write one.

`hval : c.toNat = v` says `v` is the code point of some actual character `c`, which is where all
the content lies: `v` on its own is an arbitrary natural number. Given that, the conclusion
`v < 0xD800 ∨ 0xDFFF < v` places `v` outside `D800`-`DFFF`, and it is `char_not_surrogate c`
carried along `hval`.
-/
theorem escape_not_surrogate {v : Nat} {c : Char} (hval : c.toNat = v) :
    v < 0xD800 ∨ 0xDFFF < v := by
  have := char_not_surrogate c
  omega

end

end Json.Spec
