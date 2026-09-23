# Changelog

## [Unreleased]

* Update the core library, deriving package, tests, and benchmarks for Lean 4.34.0; the optional LeanIO adapter is not included.

## [0.3.0] - 2026-08-31

* Coercions from `Nat` and `Int` to `Json` and to `Number`

## [0.2.1] - 2026-08-30

* A doc comment on every theorem, saying what it establishes and reading its statement back term by term

## [0.2.0] - 2026-08-29

* A LeanIO adapter, in `leanio/`, which makes any type with a `Json.ToJson` or `Json.FromJson` instance usable as a request body or a response

## [0.1.0] - 2026-08-20

Initial release.
