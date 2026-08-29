# JSONTestSuite

Vendored from <https://github.com/nst/JSONTestSuite>, commit `1ef36fa01286573e846ac449e8683f8833c5b26a` (2024-11-22), which accompanies Nicolas Seriot's article *Parsing JSON is a Minefield*. Copyright (c) 2016 Nicolas Seriot, MIT licence, in `LICENSE` beside this file. Only `test_parsing/` is taken; the parsers, results and article are not.

The first letter of each file name states the expected outcome:

| Prefix | Meaning |
|---|---|
| `y_` | must be accepted |
| `n_` | must be rejected |
| `i_` | either outcome is conforming, and the implementation's choice is recorded |

`Test.Conformance` runs every file and pins each outcome, including the `i_` ones, so that a change of behaviour on an unspecified case shows up as a failing test rather than passing unnoticed.
