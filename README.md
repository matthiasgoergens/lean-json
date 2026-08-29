# json

A JSON library for Lean 4: parsing, printing, querying, and `ToJson` / `FromJson` codecs, proved correct against the grammar of RFC 8259.

Nothing in it is `partial`, nothing in it can panic, and no operation walks a value on the C stack, so a document that nests a million deep is an error or a long string rather than a crash. It depends on `Init` and `Std` and on nothing in the `Lean` namespace, so a program that reads and writes JSON does not carry the Lean frontend with it. `deriving ToJson, FromJson` and the `json%` literal syntax need the frontend to elaborate, so they live in a companion package.

## Installing

In `lakefile.toml`:

```toml
[[require]]
name = "json"
git = "https://github.com/paulbutcher/lean-json.git"

# optional, for `deriving ToJson, FromJson` and `json%`
[[require]]
name = "jsonDeriving"
git = "https://github.com/paulbutcher/lean-json.git"
subDir = "deriving"
```

## Reading and writing

```lean
import Json
open Json

#eval parse "{\"a\": [1, 2.5e3], \"b\": null}"
-- Except.ok (Json.obj #[("a", ...), ("b", Json.null)])

#eval (parse "[1,2]").toOption.map compress   -- some "[1,2]"
#eval (parse "[1,2]").toOption.map pretty     -- some "[\n  1,\n  2\n]"
```

| | |
|---|---|
| `parse (s : String) (cfg : Config := {}) : Except Error Json` | |
| `parseBytes (b : ByteArray) (cfg : Config := {}) : Except Error Json` | checks UTF-8 on arrival |
| `compress (j : Json) : String` | also the `ToString` instance |
| `pretty (j : Json) (indent : Nat := 2) : String` | |
| `escape (s : String) : String` | the body of a string, unquoted |
| `renderString (s : String) : String` | quoted and escaped |

## Values

```lean
inductive Json where
  | null | bool (b : Bool) | num (n : Number)
  | str (s : String) | arr (elems : Array Json) | obj (fields : Array (String × Json))
```

An object's members keep the order they were written in, and a repeated name is representable even though a parse refuses one by default.

`Number` is a `mantissa : Int` and an `exponent : Int` denoting `mantissa * 10 ^ exponent`. The exponent is never evaluated as a power of ten, so `1e1000000000` costs nothing to hold. Every number a parse returns is canonical, meaning one spelling per value, so `==`, `compare` and `hash` cannot disagree. `toFloat`, `ofFloat?`, `toInt?` and `toNat?` convert out, the last two within a padding bound.

- Building: `mkObj`, `ofNat`, `ofInt`, coercions from `Bool`, `String` and `Number`, and numeric literals.
- Reading, each returning `Except String _`: `getBool?`, `getNum?`, `getStr?`, `getArr?`, `getObj?`, `getInt?`, `getNat?`, `getObjVal?`, `getArrVal?`, `setObjVal?`. Also `getObjValD`, `mergeObj`, `isNull`, `findLast?`, `dedupKeys`.
- Whole-value: `depth`, `uniqueKeys`, `canonicalNumbers`, `==`, `compare`, `hash`. Each keeps its pending work on the heap, so any of them answers at any depth.

## Paths

`Path := List Step`, where a `Step` is `.field (name : String)` or `.index (i : Nat)`.

```lean
#eval (parse "{\"a\":{\"b\":[7]}}").toOption.bind
  (·.get? [.field "a", .field "b", .index 0])
-- some (Json.num { mantissa := 7, exponent := 0 })
```

`get?`, `getD`, `getAs?`, `has`, `set?`, `setAs?`, `modify?`, `remove?`.

## Codecs

```lean
#eval fromJson? (α := Array Nat) (toJson #[1, 2, 3])   -- Except.ok #[1, 2, 3]
```

Instances ship for `Json`, `Number`, `Bool`, `Nat`, `Int`, `String`, `String.Slice`, `Unit`, `Empty`, `Float`, `USize`, `UInt64`, `System.FilePath`, `Structured`, `Array`, `List`, `Option`, `Prod` and `Std.TreeMap String`. `USize`, `UInt64` and `Nat` beyond the `Float` range go through `bignumToJson` / `bignumFromJson?`, which use a string to avoid a lossy round trip.

Helpers for writing instances by hand: `getObjValAs?`, `setObjValAs?`, `opt`, `getTag?`, `parseTagged`, `parseCtorFields`, `toStructured?`.

## Deriving, and literal syntax

```lean
import JsonDeriving
open Json

structure Point where
  x : Nat
  y : Nat
  label? : Option String        -- a trailing `?` makes the field optional
deriving ToJson, FromJson

#eval compress (toJson { x := 1, y := 2, label? := none : Point })   -- {"x":1,"y":2}
#eval compress (json% {here: $(({ x := 1, y := 2, label? := none } : Point)), ok: true})
```

Recursive types are derived too, through the type itself or an `Array`, `List` or `Option` of it. A field that mentions its own type in some other shape, and a group of mutually defined types, are refused at derive time rather than derived as something that might not terminate.

## Streams

`readJson (h : IO.FS.Stream) (nBytes : Nat) (cfg : Config := {})`, `readJsonToEnd`, `writeJson` and `writeJsonPretty`. Reading enforces UTF-8 where the bytes arrive, as RFC 8259 section 8.1 requires.

## Configuration

Reading is strict by default. `Json.Config` relaxes any of it.

| Setting | Default | |
|---|---|---|
| `duplicateKeys` | `.reject` | `.allow` keeps every member, in order, and lookup takes the last |
| `maxDepth` | `some 1024` | policy, not a crash guard: `none` is safe |
| `maxNumberDigits` | `some 1000` | digits of a significand or exponent; `none` is safe |
| `ignoreBOM` | `true` | RFC 8259 permits ignoring a leading `U+FEFF` |

A repeated name is refused by default because RFC 8259 leaves the outcome unspecified, so two implementations reading the same bytes can disagree about what they say.

The refusal of a lone surrogate escape such as `"\ud800"` is not configurable: it denotes no sequence of code points, so there is nothing to build.

## Guarantees

Each of these is a theorem shipped with the library, so a proof of your own can cite it.

- **One text names at most one value**: `Spec.text_unique`, a claim about the transcription of the grammar rather than about the code.
- **Whatever the parser accepts, the grammar derives**: `parse s cfg = .ok j` gives `Spec.TextOf s j` (`Parser.text_parse`, and `Parser.textOf_parseBytes` for bytes). No text is read as a value the RFC does not say it denotes.
- **Whatever the printer emits, the grammar accepts**: `CanonicalNumbers j → Spec.TextOf (compress j) j` (`Printer.textOf_compress`, and `textOf_pretty`).
- **Whatever the grammar derives, the parser reads**: `Spec.TextOf s j → parse s cfg = .ok j` (`Parser.parse_complete`), given that `maxNumberDigits` is `none`, that the value is within `maxDepth`, and that either repeated names are allowed or the value has none. Under the strict default the converse holds too: a text whose value repeats a name is refused rather than read as something else (`Parser.parse_error_of_not_uniqueKeys`).
- **Reading what was written gives back what was written**: `CanonicalNumbers j → parse (compress j) cfg = .ok j` (`parse_compress`, and `parse_pretty`), under those same three conditions.
- **What a parse returns is canonical throughout** (`Parser.canonicalNumbers_parse`), so `==`, `compare` and `hash` agree on everything it produces; and under the strict default no object in it repeats a field name (`Parser.uniqueKeys_parse`).
- **Every traversal runs iteratively.** `beq`, `hash`, `uniqueKeys`, `canonicalNumbers` and `depth` are each proved equal to a form holding its pending work in a list, and it is that form that runs (`Alg.fold_eq_run`). A claim stated about the plain recursion is therefore a claim about what the program does, at any depth.
- **Output is always valid UTF-8**, by construction, since it is a `String`.
- **The path laws**: what `set?` puts at a path is what `get?` finds there (`get?_set?`), and putting back what is already there leaves the value alone (`set?_get?`).
- **Codec round trips**: for `Json`, `Number`, `Bool`, `String` and `Unit` outright, for `Int` and `Nat` within the padding bound, and for `Option`, `Prod`, `Array` and `List` from the round trip of whatever they hold.

Not proved, and covered by tests instead:

- **Completeness, and the round trip, under a limit on significand digits.** A digit bound is a claim about the text rather than about the value, `1e2` and `100` denoting the same number at different lengths. A reading with `maxNumberDigits` set therefore has no proof that it refuses nothing else; 318 files of the JSONTestSuite conformance corpus and two 3,000 round fuzz sweeps cover it instead.
- **Absence of stack overflow and out-of-memory.** That the traversals cost heap rather than stack is by construction. Two recursions sit outside it: a codec the companion generates walks a value as a recursion, and freeing a deeply nested value is a recursion the library does not perform. Both were measured: a derived tree three million deep encodes and decodes, and a million-deep value built and dropped repeatedly leaves peak memory flat across rounds.
- `Number.toFloat` against IEEE 754, and the `Float` codec's round trip, which goes through the exact decimal expansion of a bit pattern.

## Differences vs `Lean.Data.Json`

Each row below was measured against it on Lean v4.33.1, and each is pinned by a test here.

| Input | `Lean.Data.Json` | `lean-json` |
|---|---|---|
| ten million nested arrays | `Stack overflow detected. Aborting.`, SIGABRT, exit 134, and uncatchable: the parser recurses on the C stack. A million deep survives, so where the cliff falls is a property of the stack the process happens to have rather than of the input | `.depthExceeded`, an error you can catch, or the value itself if `maxDepth` is `none`. Nesting costs heap and never stack, so the depth a reading survives is a matter of memory |
| `1e1000000000` | does not return: the exponent is evaluated as `10 ^ 1000000000` into a bignum | a `Number` with `exponent := 1000000000`, held and written back in constant time |
| `"\ud800"` | becomes `U+FFFD`. Corruption, silently, with no error to catch | `.loneSurrogate` |
| `{"a":1,"a":2}` | last wins, silently, with no way to ask for a refusal | refused by default, `.allow` to keep both |
| `{"z":1,"m":2,"a":3,"q":4}` | comes back as `z, q, m, a`: an object is a `Std.TreeMap.Raw`, so the order it was written in is gone and so is any repeated name | the order it was written in, and a repeated name if there was one |
| printing something deeply nested | `render`, which `pretty` goes through, is `partial` and recursive, so writing a value can overflow where reading it did not | one work-stack traversal, proved to be the one that runs |
| comparing or hashing something deeply nested | `beq'` and `hash'` are `partial` and recursive too | as above, for all five whole-value operations |
| `setObjVal! (num 1) "a" null` | panics | `setObjVal?`, which returns `Except String Json` |
| `toJson (1e-300 : Float)` | `0`, as is every magnitude below about `1e-7`: the encoder reads back `Float.toString`, which is fixed point, so the digits were never there. That same path calls `panic!` if the read fails | the exact decimal expansion of the bit pattern |
| `⟨15, 1⟩` against `⟨150, 2⟩`, two spellings of `1.5` where a number is `mantissa / 10 ^ exponent` | `==` is `false`, `compare` is `.eq`, and the hashes differ: a `BEq` and an `Ord` on one type that contradict each other | one canonical value per number, so `==`, `compare` and `hash` agree on everything a parse returns |

None of this is exotic input. A repeated name is what broke CouchDB in 2017 ([CVE-2017-12635](https://docs.couchdb.org/en/stable/cve/2017-12635.html)): its JavaScript and Erlang parsers resolved `{"roles":[],"roles":["_admin"]}` differently, so the write was authorised against one of the two and every later request was authorised against the other, which let any user make themselves an admin. Deep nesting and a long exponent are what a request body carries when someone is looking for a way to take a service down, and a process that aborts on `SIGABRT` cannot log, retry or return a 400.

## Speed

`bench/` times reading and writing beside `Lean.Data.Json` on the same text. Numbers from one machine, best of three, so useful for tracking rather than for comparing machines:

| Document | Size | parse | compress | pretty | core parse |
|---|---|---|---|---|---|
| numbers | 311K | 10.3ms | 11.8ms | 13.6ms | 8.6ms |
| wide object | 915K | 18.8ms | 7.1ms | 9.4ms | 17.2ms |
| strings | 1063K | 13.6ms | 5.4ms | 6.4ms | 6.9ms |
| records | 1442K | 34.8ms | 23.4ms | 36.4ms | 18.4ms |
| nesting, 20,000 deep | 39K | 0.6ms | 1.8ms | - | 0.9ms |
| long number | 195K | 61.7ms | 42.7ms | 42.5ms | 1398.0ms |

Reading runs at 30 to 77 MB/s on all but the last of those. Encoding and decoding are timed too: 20,000 records go to JSON in 4.4ms and come back in 3.2ms. Peak resident memory is about two bytes per byte of text for a document that is nearly all text, and about six for one that is nearly all value.

## Building

```
lake build          # the library
lake test           # both test suites, the library's and the companion's
cd bench && lake exe bench    # timings
```

## Licence

Apache 2.0, in `LICENSE`. The conformance corpus under `test/corpus` is [JSONTestSuite](https://github.com/nst/JSONTestSuite), copyright (c) 2016 Nicolas Seriot, MIT licence.
