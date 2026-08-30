/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Parser.Completeness
public import Json.Printer.Soundness

public section

namespace Json

/-!
Reading what was written gives back what was written.

Both halves are already proved: what the printer emits is text the grammar derives, and text the
grammar derives is read as the value the grammar gives it. The round trip is their composition,
and it holds wherever the reading refuses nothing the grammar accepts: the digit limit off,
either repeated names allowed or a value that has none, and a value within the nesting limit.
-/

variable {cfg : Config} {j : Json}

/--
Compact output is read back as the value it was printed from. This is the claim a user of the
library actually depends on, and it is not implied by the printer and the parser each being
correct in isolation: those two could agree with the grammar and still disagree with each other
about what a document means, were the grammar ambiguous.

`parse (compress j) cfg = .ok j` says the parse succeeds and returns `j` itself, not some value
equal to it in a weaker sense. The hypotheses are exactly the configurations that refuse nothing
the grammar accepts. `hdig` turns the digit limit off, since a long significand the printer will
emit is one a limit can refuse; `hkeys` asks either that `cfg` accepts repeated names or that `j`
has none, since a parser told to reject them would refuse a value carrying them; `hdepth` asks
that `j` sit within `cfg.maxDepth`, and holds with nothing to prove exactly when no limit is set,
which is the case in which no nesting can be refused; `h` asks that every number in `j` be
canonical, which is the form the printer writes and the parser reads back unchanged.
-/
theorem parse_compress (hdig : cfg.maxNumberDigits = none)
    (hkeys : cfg.duplicateKeys = .allow ∨ UniqueKeys j)
    (hdepth : ∀ limit, cfg.maxDepth = some limit → depth j ≤ limit) (h : CanonicalNumbers j) :
    parse (compress j) cfg = .ok j :=
  Parser.parse_complete hdig hkeys hdepth (Printer.textOf_compress h)

/--
Indented output is read back as the value it was printed from, so the whitespace `pretty` adds for
a human reader costs nothing in fidelity. Compact and indented output are separate functions, so
this does not follow from `parse_compress`; it is the same claim proved of the other printer.

`parse (pretty j indent) cfg = .ok j` says the parse succeeds and returns `j` itself. `indent` is
the number of spaces per level and is quantified over, so no particular choice is being relied on,
including zero. The remaining hypotheses are as in `parse_compress`: `hdig` turns the digit limit
off, `hkeys` asks that repeated names be either accepted or absent, `hdepth` asks that `j` sit
within any configured nesting limit, and `h` asks that its numbers be canonical.
-/
theorem parse_pretty (hdig : cfg.maxNumberDigits = none)
    (hkeys : cfg.duplicateKeys = .allow ∨ UniqueKeys j)
    (hdepth : ∀ limit, cfg.maxDepth = some limit → depth j ≤ limit) (h : CanonicalNumbers j)
    (indent : Nat) : parse (pretty j indent) cfg = .ok j :=
  Parser.parse_complete hdig hkeys hdepth (Printer.textOf_pretty h indent)

end Json
