/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json
public meta import JsonDeriving
public import LeanIO.Request.FromRequestBody
public import LeanIO.Response.IntoResponse
public import LeanIO.Response.BrowserCached

/-!
# `lean-json` backend for LeanIO

Importing this module makes every type with a `Json.ToJson`/`Json.FromJson`
instance usable as a JSON request body or response, and brings the
`deriving ToJson, FromJson` handlers into scope.

Import exactly one LeanIO JSON backend. Importing this alongside `LeanIO.Json.Std`
is a hard error: the generated instance names collide, and Lean reports
`environment already contains 'LeanIO.instIntoResponseOfToJson'`.
-/

namespace LeanIO
open Std.Http

public def leanJsonRender [Json.ToJson α] (a : α) : String :=
  Json.pretty (Json.toJson a)

public def leanJsonDecode [Json.FromJson α] (s : String) : Except JsonError α :=
  match Json.parse s with
  | .error e => .error (.syntax_error (toString e))
  | .ok json =>
    match Json.fromJson? (α := α) json with
    | .ok a => .ok a
    | .error e => .error (.semantic_error e)

public instance [Json.ToJson α] : IntoResponse α :=
  .ofJson leanJsonRender

public instance [Json.ToJson α] : IntoResponse (Status × α) :=
  .ofJsonWithStatus leanJsonRender

public instance [Json.ToJson α] : IntoResponse (Status × Headers × α) :=
  .ofJsonWithStatusHeaders leanJsonRender

public instance [Json.ToJson α] : IntoResponseExt (BrowserCached α) :=
  .ofJson leanJsonRender

public instance [Json.FromJson α] : FromRequestBody (Json α) :=
  .ofJson leanJsonDecode

end LeanIO
