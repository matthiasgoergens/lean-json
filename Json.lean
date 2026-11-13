/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json.Number
public import Json.Value
public import Json.Fold
public import Json.Basic
public import Json.Spec
public import Json.Spec.Follow
public import Json.Spec.Length
public import Json.Spec.Unambiguity
public import Json.Spec.Canonical
public import Json.Parser
public import Json.Printer
public import Json.FromTo
public import Json.Enum
public import Json.Strict
public import Json.Query
public import Json.Parser.Soundness
public import Json.Parser.UniqueKeys
public import Json.Parser.Completeness
public import Json.Printer.Soundness
public import Json.RoundTrip
public import Json.Stream

/-!
JSON for Lean, written to be safe on input it did not choose.

`Json.Spec` transcribes the grammar of RFC 8259. The parser is proved to accept what it derives
and nothing else, and both printers are proved to emit nothing it would refuse. Nothing here is
`partial` and nothing here panics, and the parser and the printer both keep their work on the
heap, so a document that nests a million deep is an error or a long string rather than a crash.

Reading is strict by default: a repeated field name is refused, nesting beyond 1024 is refused,
and a significand of more than a thousand digits is refused unread. `Json.Config` relaxes any of
that. `deriving ToJson, FromJson` and the `json%` literal syntax are in the companion package,
which is what keeps the frontend out of a program that only reads and writes JSON.
-/
