/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package test where
  version := v!"0.3.0"
  leanOptions := #[⟨`warningAsError, true⟩]

require jsonDeriving from ".."

require plausible from git
  "https://github.com/leanprover-community/plausible" @ "v4.34.0"

@[default_target]
lean_lib Test

@[test_driver]
lean_exe runTests where
  root := `Main
