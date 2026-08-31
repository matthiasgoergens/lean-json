/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Json
import Test.Runner

open Json
open Plausible (NamedBinder)

namespace Test.FromTo

/-! ## Behaviour -/

private def sample : Json :=
  .obj #[("name", .str "a"), ("count", .num 2)]

def values : Array TestCase := #[
  expectEq "an integer is a number, not a string" (compress (toJson (12345 : Nat))) "12345",
  expectEq "a negative integer keeps its sign" (compress (toJson (-7 : Int))) "-7",
  expectEq "unit is the empty object" (compress (toJson ())) "{}",
  expectEq "none is null" (compress (toJson (none : Option Nat))) "null",
  expectEq "some is the value itself" (compress (toJson (some 3 : Option Nat))) "3",
  expectEq "a pair is a two element array" (compress (toJson ((1, "a") : Nat × String)))
    "[1,\"a\"]",
  expectEq "a list is an array" (compress (toJson [1, 2, 3])) "[1,2,3]",
  -- Sixty-four bit integers travel as strings, since a JavaScript number would truncate them.
  expectEq "UInt64 is a string" (compress (toJson (2 ^ 63 : UInt64))) "\"9223372036854775808\"",
  expectEq "USize is a string" (compress (toJson (12 : USize))) "\"12\"",
  expectEq "a tree map is an object, in key order"
    (compress (toJson (Std.TreeMap.empty.insert "b" 2 |>.insert "a" 1 : Std.TreeMap String Nat)))
    "{\"a\":1,\"b\":2}"
]

private def decodes (name : String) (j : Json) (α : Type) [FromJson α] [BEq α] [ToString α]
    (expected : α) : TestCase :=
  { name := name
    run :=
      match (fromJson? j : Except String α) with
      | .ok v => if v == expected then pure () else throw (IO.userError s!"decoded {v}")
      | .error e => throw (IO.userError s!"failed: {e}") }

private def refuses (name : String) (j : Json) (α : Type) [FromJson α] : TestCase :=
  { name := name
    run :=
      match (fromJson? j : Except String α) with
      | .ok _ => throw (IO.userError "accepted")
      | .error _ => pure () }

def decoding : Array TestCase := #[
  decodes "a whole number decodes as a natural" (.num 12) Nat 12,
  refuses "a fraction is not a natural" (.num ⟨15, -1⟩) Nat,
  refuses "a negative number is not a natural" (.num (-1)) Nat,
  -- D21's guard, restated for codecs: a short text must not become a huge integer.
  refuses "an integer with a billion places is refused" (.num ⟨1, 1000000000⟩) Int,
  -- The guard bounds the padding, not the value, so a long integer that is really there passes.
  { name := "an integer of five hundred digits is not refused"
    run :=
      let n : Nat := 7 ^ 600
      match (fromJson? (toJson n) : Except String Nat) with
      | .ok v => if v == n then pure () else throw (IO.userError "wrong value")
      | .error e => throw (IO.userError s!"failed: {e}") },
  refuses "a number is not a string" (.num 1) String,
  refuses "an object with a field is not unit" (.obj #[("a", .null)]) Unit,
  refuses "a value too large for UInt64" (.str "18446744073709551616") UInt64,
  decodes "the largest UInt64" (.str "18446744073709551615") UInt64 (2 ^ 64 - 1),
  refuses "a non-numeral string is not a UInt64" (.str "12a") UInt64,
  -- A digit run long enough to be expensive is refused unread.
  refuses "a two thousand digit string is refused" (.str ("1".pushn '0' 2000)) UInt64,
  decodes "null decodes as none" .null (Option Nat) none,
  decodes "a missing field decodes as none"
    (getObjValD sample "absent") (Option Nat) none
]

def helpers : Array TestCase := #[
  { name := "getObjValAs? decodes the named field"
    run :=
      match getObjValAs? sample String "name" with
      | .ok v => if v == "a" then pure () else throw (IO.userError s!"got {v}")
      | .error e => throw (IO.userError e) },
  { name := "getObjValAs? reports a field of the wrong type"
    run :=
      match getObjValAs? sample Nat "name" with
      | .ok _ => throw (IO.userError "accepted a string as a natural")
      | .error _ => pure () },
  { name := "setObjValAs? replaces in place"
    run :=
      match setObjValAs? sample "count" (9 : Nat) with
      | .ok j => expectEq "" (compress j) "{\"name\":\"a\",\"count\":9}" |>.run
      | .error e => throw (IO.userError e) },
  expectEq "opt drops a missing field" (compress (mkObj (opt "k" (none : Option Nat)))) "{}",
  expectEq "opt keeps a present one" (compress (mkObj (opt "k" (some 1)))) "{\"k\":1}",
  expect "getTag? of a string is the string" (getTag? (.str "leaf") == some "leaf"),
  expect "getTag? of a single field object is its name"
    (getTag? (.obj #[("mk", .null)]) == some "mk"),
  expect "getTag? of a two field object is nothing"
    (getTag? (.obj #[("a", .null), ("b", .null)]) == none),
  expect "parseTagged reads a nullary constructor"
    ((parseTagged (.str "leaf") "leaf" 0 none).toOption == some #[]),
  expect "parseTagged rejects the wrong tag"
    ((parseTagged (.str "node") "leaf" 0 none).toOption == none),
  expect "parseTagged reads positional fields"
    ((parseTagged (.obj #[("mk", .arr #[.num 1, .num 2])]) "mk" 2 none).toOption ==
      some #[.num 1, .num 2]),
  expect "parseTagged counts the fields it was promised"
    ((parseTagged (.obj #[("mk", .arr #[.num 1])]) "mk" 2 none).toOption == none),
  expect "parseCtorFields reads named fields"
    ((parseCtorFields (.obj #[("mk", .obj #[("x", .num 1), ("y", .num 2)])]) "mk" 2
      (some #["y", "x"])).toOption == some #[.num 2, .num 1]),
  expect "toStructured? refuses a scalar"
    ((toStructured? (1 : Nat)).toOption == none),
  expect "toStructured? accepts an array"
    ((toStructured? [1, 2]).toOption == some (.arr #[.num 1, .num 2]))
]

/-! ## Floats

The exact conversion is what these check: a value below about `1e-7` reaches JSON at all, which
is the failure mode the decimal spelling of a float would introduce. -/

private def floatRoundTrips (name : String) (x : Float) : TestCase :=
  { name := name
    run :=
      match (fromJson? (toJson x) : Except String Float) with
      | .ok y => if y == x then pure () else throw (IO.userError s!"got {y}, expected {x}")
      | .error e => throw (IO.userError e) }

def floats : Array TestCase := #[
  floatRoundTrips "a tenth survives" 0.1,
  floatRoundTrips "a very small value survives" 1e-300,
  floatRoundTrips "the smallest subnormal survives" 5e-324,
  floatRoundTrips "the largest double survives" 1.7976931348623157e308,
  floatRoundTrips "zero survives" 0.0,
  floatRoundTrips "a whole number survives" 123456789.0,
  floatRoundTrips "a negative value survives" (-2.5),
  { name := "a NaN travels as a string"
    run :=
      match (fromJson? (toJson (0.0 / 0.0 : Float)) : Except String Float) with
      | .ok y => if y.isNaN then pure () else throw (IO.userError s!"got {y}")
      | .error e => throw (IO.userError e) },
  floatRoundTrips "an infinity travels as a string" (1.0 / 0.0),
  floatRoundTrips "a negative infinity too" (-1.0 / 0.0),
  -- JSON has no negative zero, so the sign is not preserved. Every implementation loses it.
  expectEq "negative zero becomes zero" (compress (toJson (-0.0 : Float))) "0"
]

/-! ## Coercions -/

-- The coercions in `Basic` and the `ToJson` instances here are separate definitions of the same
-- encoding, so they have to keep agreeing.
example (n : Nat) : ((n : Json)) = toJson n := rfl

example (i : Int) : ((i : Json)) = toJson i := rfl

/-! ## Properties -/

-- Bit patterns drawn straight from a small natural are all subnormal, the exponent field being
-- zero, so the generated values have to be spread across the range deliberately.
private def floatsOf (n : Nat) : List Float :=
  [Float.ofBits (UInt64.ofNat n),
   Float.ofBits (UInt64.ofNat (n * 0x0123456789ABCDEF)),
   Float.ofBits (UInt64.ofNat (n * 1000003 + 0x3FF0000000000000)),
   n.toFloat / 3.0,
   n.toFloat * 1e-17,
   n.toFloat * 1e17]

/-- Any bit pattern that is a number at all makes the trip, subnormals and giants included. -/
abbrev anyFloatRoundTrips : Prop :=
  NamedBinder "n" <| ∀ n : Nat,
    ((floatsOf n).all fun x =>
      x.isNaN || x.isInf ||
        (fromJson? (toJson x) : Except String Float).toOption == some x) = true

abbrev decodeNatIsInverse : Prop :=
  NamedBinder "n" <| ∀ n : Nat, decodeNat? (toString n) == some n

def all : Array TestCase :=
  values ++ decoding ++ helpers ++ floats ++ #[
    property "any float that JSON can express round trips" anyFloatRoundTrips,
    property "decodeNat? inverts the decimal spelling" decodeNatIsInverse
  ]

end Test.FromTo
