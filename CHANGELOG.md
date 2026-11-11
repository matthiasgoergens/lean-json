# Changelog

## Unreleased

* `@[json_keys]` on a structure renames the JSON keys of its derived codecs, by a convention (`snake_case`, `SCREAMING_SNAKE_CASE`, `kebab-case`, `camelCase`) and per field
* `LawfulJson`, a class for codecs that round trip, with instances for the built-in types where the round trip holds unconditionally
* Codecs for `UInt8`, `UInt16`, `UInt32` and `Fin n`, as numbers refused out of range, and a proved round trip for them and for `UInt64` and `USize`
* Deriving both codecs of a structure also proves its round trip from its fields', and derives `LawfulJson` when its field types have it
* `@[json_enum]` derives codecs that write each constructor as a string, embed other enumerations, and come with `JsonEnum` (every member, and its string) and proofs that the codec is a bijection (`LawfulJson`, `ExactJson`)

## [0.3.1] - 2026-10-18

* Chore: bump dependencies
* Update the core library, deriving package, tests, and benchmarks for Lean 4.34.0; the optional LeanIO adapter is not included.

## [0.3.0] - 2026-08-31

* Coercions from `Nat` and `Int` to `Json` and to `Number`

## [0.2.1] - 2026-08-30

* A doc comment on every theorem, saying what it establishes and reading its statement back term by term

## [0.2.0] - 2026-08-29

* A LeanIO adapter, in `leanio/`, which makes any type with a `Json.ToJson` or `Json.FromJson` instance usable as a request body or a response

## [0.1.0] - 2026-08-20

Initial release.
