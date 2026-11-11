/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Test.Runner
import Test.Codecs
import Test.Syntax
import Test.Keys
import Test.Lawful

namespace Test

def all : Array TestCase := Test.Codecs.all ++ Test.Syntax.all ++ Test.Keys.all

end Test
