/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package json where
  version := v!"0.3.0"
  leanOptions := #[⟨`warningAsError, true⟩]

@[default_target]
lean_lib Json

-- Tests live in a subproject so that nothing test-only appears in the dependency
-- graph a consumer resolves. The companion package keeps its own, run here as well so that
-- one command covers both.
@[test_driver]
script tests do
  let library ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  let libraryResult ← library.wait
  let companion ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "deriving" / "test" }
  let companionResult ← companion.wait
  return if libraryResult == 0 then companionResult else libraryResult
