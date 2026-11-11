/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import JsonDeriving

public section

namespace Test.EnumModule

/-- Declared in a module of its own, to be embedded across a module boundary. -/
@[json_enum SCREAMING_SNAKE_CASE]
inductive Inner where
  | badRequest
  | geometryAmbiguous
deriving Json.ToJson, Json.FromJson

end Test.EnumModule
