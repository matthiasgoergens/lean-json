/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package jsonDeriving where
  version := v!"0.3.0"
  leanOptions := #[⟨`warningAsError, true⟩]

require json from ".."

@[default_target]
lean_lib JsonDeriving where
  roots := #[`JsonDeriving]
  globs := #[.andSubmodules `JsonDeriving]

-- As in the root package, tests are a subproject, so that nothing test-only appears in the
-- dependency graph a consumer resolves.
@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait
