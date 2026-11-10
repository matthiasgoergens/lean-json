/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json
public import JsonDeriving.Keys
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util

public section

namespace Json.Deriving

open Lean Elab Command Term Meta

/-!
Enumerations, the inductive types marked `json_enum`, whose constructors carry nothing, or one
argument that is itself an enumeration, each written as a JSON string. An embedded enumeration's
members are listed in the outer type as constructor applications, each under the inner member's
string, so the outer type's codecs and proofs never unfold the inner type's: they are
self-contained however deep the embedding goes, and cost what the members do.
-/

/-- One value of an enumeration: the constructors applied, outermost first, and its string. -/
meta structure EnumMember where
  path : Array Name
  string : String
deriving Inhabited

/-- The members of every enumeration whose codec was derived, for an outer type to embed. -/
private meta initialize enumCodecs :
    SimplePersistentEnvExtension (Name × Array EnumMember) (NameMap (Array EnumMember)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (decl, members) => m.insert decl members
    addImportedFn := fun modules => modules.foldl (init := {}) fun m entries =>
      entries.foldl (init := m) fun m (decl, members) => m.insert decl members
  }

meta def recordEnum (declName : Name) (members : Array EnumMember) : CommandElabM Unit :=
  modifyEnv (enumCodecs.addEntry · (declName, members))

/--
The last components of the names a derived enumeration adds under its own, which a constructor
cannot also be called. A constructor with one of them is refused, where the clash would otherwise
surface as a redeclaration and a cascade of type errors.
-/
meta def enumDeclSuffixes : List String :=
  ["toJsonString", "all", "mem_all", "nodup_all", "jsonKey", "jsonKeyTree", "ofJsonString?",
    "stringKey?_toJsonString", "find?_jsonKey", "ofJsonString?_toJsonString",
    "eq_toJson_of_fromJson?"]

private meta def ctorString (ctorName : Name) : MetaM String :=
  match ctorName.eraseMacroScopes with
  | .str _ s => return s
  | n => throwError "cannot derive a JSON codec for the constructor name {n}"

/--
The members of `declName` if it carries `json_enum`: every constructor nullary, or carrying one
argument of an enumeration derived already; a type with the attribute of any other shape is
refused. A type without it is derived as any other inductive type, nullary constructors included.
-/
meta def enumMembers? (declName : Name) : MetaM (Option (Array EnumMember)) := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? declName | return none
  if isStructure env declName then return none
  let some naming := enumNaming? env declName | return none
  let refuse {α} (why : MessageData) : MetaM (Option α) :=
    throwError "cannot derive a JSON enumeration for {declName}: {why}"
  if info.numParams != 0 || info.numIndices != 0 then
    return ← refuse "it has parameters or indices"
  let mut members := #[]
  for ctorName in info.ctors do
    let ctor ← getConstInfoCtor ctorName
    let short ← ctorString ctorName
    let overridden := naming.overrides.any (·.1 == Name.mkSimple short)
    if enumDeclSuffixes.contains short then
      return ← refuse m!"the constructor {ctorName} has the name of a declaration the \
derivation adds, {declName ++ Name.mkSimple short}; rename the constructor"
    match ctor.numFields with
    | 0 =>
      let string := naming.apply (.mkSimple short) short
      if string.isEmpty && !overridden then
        return ← refuse m!"the constructor {ctorName} would be written as the empty string; give \
it a string of its own"
      members := members.push { path := #[ctorName], string }
    | 1 =>
      let inner? ← forallTelescopeReducing ctor.type fun xs _ => do
        let some x := xs[0]? | return none
        let type ← whnf (← inferType x)
        return type.constName?
      let some inner := inner? |
        return ← refuse m!"the argument of {ctorName} is not of an enumeration"
      if inner == declName then
        return ← refuse m!"{ctorName} takes {declName} itself as its argument, and an enumeration \
cannot contain itself"
      let some innerMembers := (enumCodecs.getState env).find? inner |
        return ← refuse m!"the argument of {ctorName} is of type {inner}, which has no derived \
JSON enumeration codec, so derive it first, under json_enum"
      if overridden then
        throwError "cannot derive a JSON enumeration for {declName}: {ctorName} is written as its \
argument is, and takes no string of its own"
      members := members ++ innerMembers.map fun m => { m with path := #[ctorName] ++ m.path }
    | _ => return ← refuse m!"{ctorName} has more than one argument"
  -- Two members on one string would read back as whichever the decoder finds first.
  let mut seen : Std.HashMap String (Array Name) := {}
  for m in members do
    if let some other := seen[m.string]? then
      throwError "cannot derive a JSON enumeration for {declName}: {showPath other} and \
{showPath m.path} would both be written as {repr m.string}"
    seen := seen.insert m.string m.path
  return some members
where
  showPath (path : Array Name) : String := " ".intercalate (path.toList.map toString)

/-- The byte key `Json.stringKey?` gives a string within its bound. -/
private meta def stringKey (s : String) : Nat :=
  s.toUTF8.foldl (fun acc b => acc * 257 + b.toNat + 1) 0

private meta def maxBytes (members : Array EnumMember) : Nat :=
  members.foldl (fun n m => max n m.string.utf8ByteSize) 0

/-- A member as a term, or as a pattern. -/
private meta def memberTerm (path : Array Name) : MetaM Term := do
  let some last := path.back? | throwError "an enumeration member with no constructor"
  path.pop.foldrM (init := ← `($(mkCIdent last):ident)) fun c inner =>
    `($(mkCIdent c):ident $inner)

/-- The name `T.suffix` for a declaration about `declName`, and whether it is private. -/
private meta def companion (declName : Name) (suffix : String) :
    MetaM (Ident × Option (TSyntax ``Parser.Command.visibility)) := do
  let name := privateToUserName declName |>.str suffix
  let visibility ← if isPrivateName declName then
      some <$> `(Parser.Command.visibility| private)
    else pure none
  return (mkIdent (`_root_ ++ name), visibility)

/-- The alternatives of a function of a member, one per member. -/
private meta def matchOn (x : Ident) (members : Array EnumMember)
    (rhs : Nat → EnumMember → MetaM Term) : MetaM Term := do
  if members.isEmpty then return ← `(nomatch $x:ident)
  let pats ← members.mapM (memberTerm ·.path)
  let rhss ← members.mapIdxM rhs
  `(match $x:ident with $[| $pats => $rhss]*)

/--
A list as a balanced tree of appends of singletons, so that a member is shown to be in it by a
path of logarithmic length, where finding it in a list literal takes as many steps as its index.
-/
private meta def appendTree (elems : Array Term) : MetaM Term := do
  if h : elems.size = 0 then `([]) else
  if h1 : elems.size = 1 then `([$(elems[0])]) else
  let mid := elems.size / 2
  `($(← appendTree (elems.extract 0 mid)) ++ $(← appendTree (elems.extract mid elems.size)))
termination_by elems.size
decreasing_by all_goals (simp only [Array.size_extract]; omega)

/-- That the element at index `i` of `appendTree` of `n` elements is in it. -/
private meta def memProof (n i : Nat) : MetaM Term := do
  if n ≤ 1 then `(List.mem_singleton_self _) else
  let mid := n / 2
  if i < mid then `(List.mem_append_left _ $(← memProof mid i))
  else `(List.mem_append_right _ $(← memProof (n - mid) (i - mid)))
termination_by n
decreasing_by all_goals omega

open TSyntax.Compat in
/--
`T.toJsonString`, `T.all` and `T.mem_all`, and the `JsonEnum` and `NonNullJson` instances, given
the encoder `aux` the `ToJson` instance is built on.
-/
meta def mkEnumToJsonCmds (declName : Name) (members : Array EnumMember) (aux : Ident) :
    MetaM (Array Command × Array Command) := do
  let indType := mkCIdent declName
  let x := mkIdent `x
  let (toStr, vis) ← companion declName "toJsonString"
  let (all, _) ← companion declName "all"
  let (memAll, _) ← companion declName "mem_all"
  let (nodupAll, _) ← companion declName "nodup_all"
  let strBody ← matchOn x members fun _ m => pure (Lean.quote m.string)
  let toStrCmd ← `(
    /-- The string a value is written as. -/
    @[expose] $[$vis:visibility]? def $toStr:ident ($x : $indType) : String := $strBody)
  let auxCmd ← `(@[expose] def $aux:ident ($x : $indType) : _root_.Json :=
    _root_.Json.str ($toStr $x))
  let elems ← members.mapM (memberTerm ·.path)
  let allCmd ← `(
    /-- Every value, in the order of declaration, an embedded enumeration's in its own. -/
    @[expose] $[$vis:visibility]? def $all:ident : List $indType := $(← appendTree elems))
  let memBody ← matchOn x members fun i _ => memProof elems.size i
  let memCmd ← `(
    /--
    Every value is in the list of all of them, which is what lets a caller enumerate the type.

    `x ∈ all` is membership of the list; each value is found by its path down the tree of appends
    the list is built as.
    -/
    $[$vis:visibility]? theorem $memAll:ident ($x : $indType) : $x ∈ $all := $memBody)
  -- Each value's position in `all` is its own, so `all` has no repeats: positions are `range n`.
  let position ← matchOn x members fun i _ => pure (quote i)
  let n := quote members.size
  let nodupCmd ← `(
    /--
    No value is in the list of all of them twice.

    `Nodup` says no two entries of the list are equal. Each value's position in `all` is computed
    by a `match`, and the positions of the list are `0` to `n - 1` in order, checked by one
    evaluation in the kernel; entries with different positions are different.
    -/
    $[$vis:visibility]? theorem $nodupAll:ident : ($all).Nodup := by
      have h : ($all).map (fun $x:ident => $position) = List.range $n := by decide +kernel
      exact List.Pairwise.of_map (fun $x:ident => $position)
        (fun a b hne heq => hne (by rw [heq])) (h ▸ List.nodup_range))
  let enumCmd ← `(instance : _root_.Json.JsonEnum $indType where
    all := $all
    mem_all := $memAll
    nodup_all := $nodupAll
    toJsonString := $toStr
    toJson_eq_str _ := rfl)
  let nonNullCmd ← `(instance : _root_.Json.NonNullJson $indType := ⟨fun _ => nofun⟩)
  return (#[toStrCmd, auxCmd], #[allCmd, memCmd, nodupCmd, enumCmd, nonNullCmd])

/-- The lookup from byte key to member, a balanced `KeyTree` over the sorted keys. -/
private meta def keyTree (sorted : Array (Nat × EnumMember)) : MetaM Term := do
  if h : sorted.size = 0 then `(_root_.Json.KeyTree.empty) else
  if h1 : sorted.size = 1 then
    `(_root_.Json.KeyTree.leaf $(← memberTerm sorted[0].2.path))
  else
    let mid := sorted.size / 2
    let some (pivot, _) := sorted[mid]? | `(_root_.Json.KeyTree.empty)
    `(_root_.Json.KeyTree.node $(quote pivot) $(← keyTree (sorted.extract 0 mid))
      $(← keyTree (sorted.extract mid sorted.size)))
termination_by sorted.size
decreasing_by all_goals (simp only [Array.size_extract]; omega)

open TSyntax.Compat in
/--
`T.jsonKey`, `T.jsonKeyTree` and `T.ofJsonString?`, and the decoder `aux` the `FromJson` instance
uses.
-/
meta def mkEnumFromJsonCmds (declName : Name) (members : Array EnumMember) (aux : Ident) :
    MetaM (Array Command) := do
  let indType := mkCIdent declName
  let x := mkIdent `x
  let (key, vis) ← companion declName "jsonKey"
  let (tree, _) ← companion declName "jsonKeyTree"
  let (ofStr, _) ← companion declName "ofJsonString?"
  let keyBody ← matchOn x members fun _ m => pure (quote (stringKey m.string))
  let sorted := (members.map fun m => (stringKey m.string, m)).qsort (·.1 < ·.1)
  let typeName := Lean.quote (toString declName)
  let keyCmd ← `(
    /-- The key of a value's string, which the decoder looks the string up by. -/
    @[expose] $[$vis:visibility]? def $key:ident ($x : $indType) : Nat := $keyBody)
  let treeCmd ← `(
    @[expose] $[$vis:visibility]? def $tree:ident : _root_.Json.KeyTree $indType :=
      $(← keyTree sorted))
  let ofStrCmd ← `(
    /-- The member written as the string, or an error naming the type and the string. -/
    @[expose] $[$vis:visibility]? def $ofStr:ident : String → Except String $indType :=
      _root_.Json.decodeByKey $typeName $(quote (maxBytes members))
        (fun k => _root_.Json.KeyTree.find? $key k $tree))
  let auxCmd ← `(@[expose] def $aux:ident : _root_.Json → Except String $indType :=
    _root_.Json.enumFromJson? $typeName $ofStr)
  return #[keyCmd, treeCmd, ofStrCmd, auxCmd]

open TSyntax.Compat in
/--
The round trip, that the decoder accepts nothing else, and the `LawfulJson` and `ExactJson`
instances. Both rest on two facts per member: its string has its key, evaluated once in the
kernel, and the tree finds it under that key, a path of logarithmic length. No two strings are
ever compared.
-/
meta def mkEnumRoundTripCmds (declName : Name) (members : Array EnumMember) :
    MetaM (Array Command) := do
  let indType := mkCIdent declName
  let x := mkIdent `x
  let j := mkIdent `j
  let h := mkIdent `h
  let (toStr, vis) ← companion declName "toJsonString"
  let (key, _) ← companion declName "jsonKey"
  let (tree, _) ← companion declName "jsonKeyTree"
  let (ofStr, _) ← companion declName "ofJsonString?"
  let (keyThm, _) ← companion declName "stringKey?_toJsonString"
  let (findThm, _) ← companion declName "find?_jsonKey"
  let (thm, _) ← companion declName "ofJsonString?_toJsonString"
  let (exact, _) ← companion declName "eq_toJson_of_fromJson?"
  let bound := quote (maxBytes members)
  let keyBody ← matchOn x members fun _ _ => `(by decide +kernel)
  let findBody ← matchOn x members fun _ _ => `(rfl)
  let keyCmd ← `(
    /--
    Every value's string has the key the decoder's tree holds it under.

    `stringKey? _ (toJsonString x)` is the key of the string `x` is written as, within the
    decoder's bound; `some (jsonKey x)` is the key the tree compares it with. Each case is one
    evaluation in the kernel.
    -/
    $[$vis:visibility]? theorem $keyThm:ident ($x : $indType) :
        _root_.Json.stringKey? $bound ($toStr $x) = some ($key $x) := $keyBody)
  let findCmd ← `(
    /--
    The decoder's tree finds every value under its key, which is what makes the decoder total on
    the members' strings.

    `find?` follows the tree from the root by comparisons of numbers; `some x` says it reaches the
    leaf holding `x`. Each case evaluates one path.
    -/
    $[$vis:visibility]? theorem $findThm:ident ($x : $indType) :
        _root_.Json.KeyTree.find? $key ($key $x) $tree = some $x := $findBody)
  let thmCmd ← `(
    /--
    Every value reads back from its string, so the string can stand for the value in any text.

    `ofJsonString? (toJsonString x)` decodes the string `x` is written as, and `.ok x` says it
    yields `x` itself: the string has `x`'s key, and the tree finds `x` under it.
    -/
    $[$vis:visibility]? theorem $thm:ident ($x : $indType) :
        $ofStr ($toStr $x) = Except.ok $x :=
      _root_.Json.decodeByKey_of_key ($keyThm $x) ($findThm $x))
  let exactCmd ← `(
    /--
    The decoder accepts only the members' strings, each as its own member, so with the round trip
    the codec is a bijection between values and their strings.

    `fromJson? j = .ok x` says the decoder accepted `j` as `x`; `j = toJson x` says `j` is exactly
    the JSON string `x` is written as. It follows from the keys of the members' strings and the
    injectivity of the key, by `Json.enumFromJson?_sound`.
    -/
    $[$vis:visibility]? theorem $exact:ident ($j : _root_.Json) ($x : $indType)
        ($h : (_root_.Json.FromJson.fromJson? $j : Except String $indType) = Except.ok $x) :
        $j = _root_.Json.ToJson.toJson $x :=
      _root_.Json.enumFromJson?_sound $keyThm $h)
  let lawfulCmd ← `(instance : _root_.Json.LawfulJson $indType := ⟨fun $x:ident => $thm $x⟩)
  let exactInst ← `(instance : _root_.Json.ExactJson $indType := ⟨$exact⟩)
  return #[keyCmd, findCmd, thmCmd, exactCmd, lawfulCmd, exactInst]

end Json.Deriving
