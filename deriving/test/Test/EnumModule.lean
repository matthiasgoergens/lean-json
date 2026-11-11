/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Test.EnumModuleInner

public section

namespace Test.EnumModule

open Json

/-- An enumeration embedding one from another module, whose definitions it never unfolds. -/
@[json_enum snake_case]
inductive Outer where
  | inner (i : Inner)
  | readName
deriving ToJson, FromJson

example : LawfulJson Outer := inferInstance
example : LawfulJson Inner := inferInstance
example : (JsonEnum.all : List Outer).map toJsonString =
    ["BAD_REQUEST", "GEOMETRY_AMBIGUOUS", "read_name"] := rfl

end Test.EnumModule
