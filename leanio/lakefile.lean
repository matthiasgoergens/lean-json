/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake
open Lake DSL

package leanioJson where
  version := v!"0.2.0"
  leanOptions := #[⟨`warningAsError, true⟩]

require json from ".."
require jsonDeriving from "../deriving"
require leanio from git "https://github.com/paulbutcher/leanio.git" @ "json2"

@[default_target]
lean_lib LeanIOJson
