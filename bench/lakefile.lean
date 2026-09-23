/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package bench where
  version := v!"0.3.0"
  leanOptions := #[⟨`warningAsError, true⟩]

require json from ".."
require jsonDeriving from "../deriving"

-- A subproject, like the tests, so that nothing here reaches a consumer. It is the one place
-- allowed to import the Lean package, since comparing against `Lean.Data.Json` is the point.
@[default_target]
lean_exe bench where
  root := `Main
