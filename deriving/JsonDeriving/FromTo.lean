/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Json
public import JsonDeriving.Keys
public import JsonDeriving.Enum
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util
public meta import Lean.Meta.StringLitProof

public section

namespace Json.Deriving

open Lean Elab Command Term Meta Parser.Term
open Lean.Elab.Deriving

/-!
Handlers for `deriving ToJson, FromJson`.

Neither generated function is `partial`. An encoder recurses on the value, which is structural.
A decoder for a recursive type recurses on the text, where nothing tells Lean that a field is
smaller than the value it came out of, so it takes a count instead, and the instance passes the
depth of what it was handed. That count is never what stops it: every step descends at least one
level, so it cannot run out before the value does. A type that cannot recurse gets neither the
count nor the traversal that works out what it should be.
-/

private meta def mentions (indName : Name) (type : Expr) : Bool :=
  (type.find? (·.isConstOf indName)).isSome

private meta def containerArg? (container : Name) (type : Expr) : Option Expr :=
  if type.isAppOfArity container 1 then type.getAppArgs[0]? else none

/-- A field whose type mentions the one being derived, in a shape with no code to generate. -/
private meta def unsupportedField (indName : Name) (type : Expr) : TermElabM α :=
  throwError "cannot derive a JSON codec for {indName}: a field of type {type} refers to \
{indName} in a shape this handler does not cover. Recursion is generated through a field of \
type {indName} itself, or of `Array`, `List` or `Option` of it; anything else has to be \
written by hand."

/-- How one field becomes JSON: through the function being defined, or through an instance. -/
private meta def encodeField (indName : Name) (aux : Ident) (x : Term) (type : Expr) :
    TermElabM Term := do
  if type.isAppOf indName then
    `($aux $x)
  else if let some inner := containerArg? ``Array type then
    if inner.isAppOf indName then `(_root_.Json.arr (($x).map $aux)) else viaInstance x type
  else if let some inner := containerArg? ``List type then
    if inner.isAppOf indName then `(_root_.Json.arr ((($x).map $aux).toArray))
    else viaInstance x type
  else if let some inner := containerArg? ``Option type then
    if inner.isAppOf indName then
      -- A `match` rather than `Option.map`, because a recursive call passed as an argument
      -- defeats the structural recursion the generated encoder relies on.
      let v := mkIdent (← mkFreshUserName `v)
      `(match $x:term with | none => _root_.Json.null | some $v => $aux $v)
    else viaInstance x type
  else
    viaInstance x type
where
  viaInstance (x : Term) (type : Expr) : TermElabM Term := do
    if mentions indName type then unsupportedField indName type else `(_root_.Json.ToJson.toJson $x)

/-- How one field is read back, with whatever count the enclosing call has left. -/
private meta def decodeField (indName : Name) (aux : Ident) (fuel : Ident) (j : Term)
    (type : Expr) : TermElabM Term := do
  if type.isAppOf indName then
    `($aux $fuel $j)
  else if let some inner := containerArg? ``Array type then
    if inner.isAppOf indName then `(_root_.Json.arrayOf? ($aux $fuel) $j) else viaInstance j type
  else if let some inner := containerArg? ``List type then
    if inner.isAppOf indName then `(_root_.Json.listOf? ($aux $fuel) $j) else viaInstance j type
  else if let some inner := containerArg? ``Option type then
    if inner.isAppOf indName then `(_root_.Json.optionOf? ($aux $fuel) $j) else viaInstance j type
  else
    viaInstance j type
where
  viaInstance (j : Term) (type : Expr) : TermElabM Term := do
    if mentions indName type then unsupportedField indName type
    else `(_root_.Json.FromJson.fromJson? $j)

/--
A field named with a trailing `?` is optional, and drops out of the object when absent. Its key is
the one `json_keys` gives it, else its name without the `?` under the structure's convention.
-/
private meta def jsonFieldName (indName : Name) (n : Name) : TermElabM (Bool × Term) := do
  let .str .anonymous s := n | throwError "cannot derive a JSON codec for the field name {n}"
  let stripped := s.dropEndWhile (· == '?') |>.copy
  let naming := keyNaming (← getEnv) indName
  let key := naming.apply n stripped
  return (s != stripped, Lean.quote key)

/-- Two fields under one key would make an object that reads back as something else. -/
private meta def checkKeysDistinct (indName : Name) (fields : Array Name) : TermElabM Unit := do
  let keys ← fields.mapM fun field => do
    let (_, key) ← jsonFieldName indName field
    return (field, key.raw.isStrLit?.getD "")
  for h : i in *...keys.size do
    for (other, key) in keys.extract 0 i do
      if key == keys[i].2 then
        throwError "cannot derive a JSON codec for {indName}: the fields {other} and \
{keys[i].1} would both be written as \"{key}\""

/--
The name a strict decoder reports and the list of keys it knows, which are the keys its encoder
writes, or `none` for a structure without `strict`.
-/
private meta def strictKeys? (indName : Name) (fields : Array Name) :
    TermElabM (Option (Term × Term)) := do
  unless (keyNaming (← getEnv) indName).strict do return none
  let keys ← fields.mapM fun field => return (← jsonFieldName indName field).2
  return some (Lean.quote (toString (privateToUserName indName)), ← `([$keys,*]))

private meta def theOnlyType (ctx : Deriving.Context) (indName : Name) :
    TermElabM InductiveVal := do
  match ctx.typeInfos[0]?, ctx.typeInfos.size == 1 with
  | some indVal, true => return indVal
  | _, _ =>
    throwError "cannot derive a JSON codec for {indName}, which is defined mutually with other \
types. Write the instances by hand."

/-- The declared type of a structure field, which says whether the codec has to recurse. -/
private meta def fieldType (indName : Name) (field : Name) : TermElabM Expr := do
  let some info := getStructureInfo? (← getEnv) indName |
    throwError "{indName} is not a structure"
  let some fieldInfo := info.fieldInfo.find? (·.fieldName == field) |
    throwError "cannot find the field {field} of {indName}"
  let projInfo ← getConstInfo fieldInfo.projFn
  forallTelescopeReducing projInfo.type fun xs _ => do
    let some self := xs.back? | throwError "cannot read the type of {field}"
    inferType (mkAppN (mkConst fieldInfo.projFn (projInfo.levelParams.map mkLevelParam))
      (xs.pop.push self))

/-! ## Encoding -/

private meta def mkToJsonBodyForStruct (indName : Name) (aux : Ident) (header : Header) :
    TermElabM Term := do
  let target := mkIdent header.targetNames[0]!
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  checkKeysDistinct indName fields
  let parts ← fields.mapM fun field => do
    let (isOptional, name) ← jsonFieldName indName field
    let type ← fieldType indName field
    let access ← `(($target).$(mkIdent field):ident)
    if isOptional then
      if mentions indName type then unsupportedField indName type
      else `(_root_.Json.opt $name $access)
    else
      let encoded ← encodeField indName aux access type
      `([($name, $encoded)])
  `(_root_.Json.mkObj <| List.flatten [$parts,*])

private meta def mkToJsonBodyForInduct (indVal : InductiveVal) (aux : Ident) (header : Header) :
    TermElabM Term := do
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts indVal fun ctor args userNames => do
    let ctorName := Lean.quote ctor.name.eraseMacroScopes.getString!
    match args, userNames with
    | #[], _ => `(_root_.Json.str $ctorName)
    | #[(x, t)], none =>
      let encoded ← encodeField indVal.name aux x t
      `(_root_.Json.mkObj [($ctorName, $encoded)])
    | xs, none =>
      let encoded ← xs.mapM fun (x, t) => encodeField indVal.name aux x t
      `(_root_.Json.mkObj [($ctorName, _root_.Json.arr #[$[$encoded:term],*])])
    | xs, some userNames =>
      let named ← xs.mapIdxM fun i (x, t) => do
        let name := Lean.quote userNames[i]!.eraseMacroScopes.getString!
        let encoded ← encodeField indVal.name aux x t
        `(($name, $encoded))
      `(_root_.Json.mkObj [($ctorName, _root_.Json.mkObj [$[$named:term],*])])
  `(match $[$discrs],* with $alts:matchAlt*)
where
  -- One alternative per constructor, each binding its fields and carrying their types along.
  mkAlts (indVal : InductiveVal)
      (rhs : ConstructorVal → Array (Ident × Expr) → Option (Array Name) → TermElabM Term) :
      TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let ctorInfo ← getConstInfoCtor ctorName
      let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
        let mut patterns := #[]
        for _ in *...indVal.numIndices do
          patterns := patterns.push (← `(_))
        let mut ctorArgs := #[]
        for _ in *...indVal.numParams do
          ctorArgs := ctorArgs.push (← `(_))
        let mut binders := #[]
        let mut userNames := #[]
        for i in *...ctorInfo.numFields do
          let x := xs[indVal.numParams + i]!
          let localDecl ← x.fvarId!.getDecl
          if !localDecl.userName.hasMacroScopes then
            userNames := userNames.push localDecl.userName
          let a := mkIdent (← mkFreshUserName `a)
          binders := binders.push (a, localDecl.type)
          ctorArgs := ctorArgs.push a
        patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
        let rhs ← rhs ctorInfo binders
          (if userNames.size == binders.size then some userNames else none)
        `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
      alts := alts.push alt
    return alts

/-! ## Decoding -/

private meta def mkFromJsonBodyForStruct (indName : Name) (aux : Ident) (fuel : Ident)
    (json : Ident) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  checkKeysDistinct indName fields
  let getters : Array (TSyntax `doElem) ← fields.mapM fun field => do
    let (_, name) ← jsonFieldName indName field
    let type ← fieldType indName field
    let source ← `(($json).getObjValD $name)
    let decoded ← decodeField indName aux fuel source type
    let label := Lean.quote s!"{indName}.{field}: "
    `(doElem| Except.mapError (fun s => $label ++ s) <| $decoded)
  let names := fields.map mkIdent
  match ← strictKeys? indName fields with
  | some (typeName, known) =>
    `(do
      _root_.Json.checkKnownKeys $typeName $known $json
      $[let $names:ident ← $getters]*
      return { $[$names:ident := $(id names)],* })
  | none =>
    `(do
      $[let $names:ident ← $getters]*
      return { $[$names:ident := $(id names)],* })

private meta def mkFromJsonBodyForInduct (indVal : InductiveVal) (aux : Ident) (fuel : Ident)
    (json : Ident) : TermElabM Term := do
  let mut alts := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let ctorStr := ctorName.eraseMacroScopes.getString!
    let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
      let mut binders := #[]
      let mut userNames := #[]
      for i in *...ctorInfo.numFields do
        let x := xs[indVal.numParams + i]!
        let localDecl ← x.fvarId!.getDecl
        if !localDecl.userName.hasMacroScopes then
          userNames := userNames.push localDecl.userName
        binders := binders.push (mkIdent (← mkFreshUserName `a), localDecl.type)
      let names := binders.map Prod.fst
      let namesOpt ←
        if binders.size == userNames.size then
          let quoted := userNames.map fun n => Lean.quote n.eraseMacroScopes.getString!
          `(some #[$[$quoted:term],*])
        else
          `(none)
      let body ←
        if ctorInfo.numFields == 0 then
          `(return $(mkIdent ctorName):ident)
        else
          let reads : Array (TSyntax `doElem) ← binders.mapIdxM fun i (_, type) => do
            let source ← `(← _root_.Json.ctorField? fields $(Lean.quote i))
            let decoded ← decodeField indVal.name aux fuel source type
            let step ← `(Lean.Parser.Term.doExpr| $decoded:term)
            `(doElem| let $(names[i]!):ident ← $step:doExpr)
          `((_root_.Json.parseCtorFields $json $(Lean.quote ctorStr)
              $(Lean.quote ctorInfo.numFields) $namesOpt).bind fun fields => do
              $[$reads:doElem]*
              return $(mkIdent ctorName):ident $names*)
      return (ctorStr, body, ctorInfo.numFields)
    alts := alts.push alt
  -- Constructors with fewer fields first, since those are the cheaper matches.
  let sorted := alts.qsort (fun (_, _, x) (_, _, y) => x < y)
  let tags := sorted.map fun (tag, _, _) => Lean.quote tag
  let bodies := sorted.map fun (_, body, _) => body
  let unknown := Lean.quote s!"no constructor of {indVal.name} has that name"
  `(match _root_.Json.getTag? $json with
    | some tag =>
      match tag with
      $[| $tags:term => $bodies:term]*
      | _ => Except.error $unknown
    | none => Except.error "expected a string, or an object of one field, naming a constructor")

/-! ## Round trips

Once both codecs of a structure are derived, the second handler to run adds
`T.fromJson?_toJson`, the round trip for one value given the round trip of each of its fields,
and a `LawfulJson` instance when every field type has one. The proof finds each field by its key
in the encoded object and rewrites the decoder with what it finds. A structure gets neither when a
field's type depends on another field's value, which defeats rewriting under the decoder's
binders, or when it has an instance parameter, which the generated binders cannot supply; nor
does an inductive type with constructors, whose proof would have to follow the tag dispatch,
unless it is an enumeration, whose round trip `JsonDeriving.Enum` proves.
-/

/--
A proof that two different string literals differ, which the generated proofs need of every pair
of keys. A tactic for each pair would cost more than the rest of the proof put together.
-/
syntax (name := keysNe) "json_keys_ne% " str ppSpace str : term

@[term_elab keysNe] meta def elabKeysNe : Term.TermElab := fun stx _ => do
  match stx with
  | `(json_keys_ne% $a:str $b:str) =>
    if a.getString == b.getString then throwError "the keys {a} and {b} are the same"
    mkStringLitNeProof a.getString b.getString
  | _ => throwUnsupportedSyntax

/--
The encoder or decoder function derived for each type, by class, so that the second handler can
find what the first defined: a hand-written instance is nothing the proof could unfold.
-/
private meta initialize derivedCodecs :
    SimplePersistentEnvExtension (Name × Name × Name) (Std.HashMap (Name × Name) Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (cls, decl, aux) => m.insert (cls, decl) aux
    addImportedFn := fun modules => modules.foldl (init := {}) fun m entries =>
      entries.foldl (init := m) fun m (cls, decl, aux) => m.insert (cls, decl) aux
  }

private meta def derivedCodec? (env : Environment) (cls decl : Name) : Option Name :=
  (derivedCodecs.getState env)[(cls, decl)]?

/--
The types of the fields of `x`, or `none` if one of them depends on the value through an
earlier field.
-/
private meta def independentFieldTypes (fields : Array Name) (x : Expr) :
    TermElabM (Option (Array Expr)) := do
  let types ← fields.mapM fun field => do
    inferType (← mkProjection x field)
  let x := x.fvarId!
  return if types.any (·.containsFVar x) then none else some types

/-- Whether `LawfulJson` is known for `type`, in the local context of the instance. -/
private meta def hasLawful (type : Expr) : TermElabM Bool := do
  try
    let inst ← mkAppOptM ``_root_.Json.LawfulJson #[some type, none, none]
    return (← synthInstance? inst).isSome
  catch _ =>
    return false

open TSyntax.Compat in
private meta def mkRoundTripCmds (declName fromAux : Name) : TermElabM (Array Command) := do
  if let some members ← enumMembers? declName then
    return ← mkEnumRoundTripCmds declName members
  let env ← getEnv
  let indVal ← getConstInfoInduct declName
  if !isStructure env declName || indVal.isRec then return #[]
  -- The generated binders leave a parameter's type to be inferred, and one inferred that way is
  -- not a local instance, so a field projection asking for it would fail.
  let instParam ← forallBoundedTelescope indVal.type indVal.numParams fun xs _ =>
    xs.anyM fun x => return (← x.fvarId!.getDecl).binderInfo.isInstImplicit
  if instParam then return #[]
  let fields := getStructureFieldsFlattened env declName (includeSubobjectFields := false)
  let argNames ← mkInductArgNames indVal
  let indType ← mkInductiveApp indVal argNames
  let mut valueName := `x
  while fields.contains valueName do
    valueName := valueName.appendAfter "'"
  let x := mkIdent valueName
  let codecBinders := (← mkImplicitBinders argNames) ++
    (← mkInstImplicitBinders ``_root_.Json.ToJson indVal argNames) ++
    (← mkInstImplicitBinders ``_root_.Json.FromJson indVal argNames)
  let lawfulBinders := codecBinders ++
    (← mkInstImplicitBinders ``_root_.Json.LawfulJson indVal argNames)
  -- A parameter that an optional field holds has to be `NonNullJson` as well, which is asked only
  -- where it is needed, so as not to narrow the instance for every other structure.
  let nonNullBinders := lawfulBinders ++
    (← mkInstImplicitBinders ``_root_.Json.NonNullJson indVal argNames)
  let valueBinder ← `(bracketedBinderF|($x : $indType))
  -- Whether a field type depends on the value, and whether every one is lawful, are both asked
  -- in the context the instance would be declared in.
  let lawfulUnder (binders : Array (TSyntax ``bracketedBinder)) : TermElabM (Option Bool) :=
    Term.elabBinders (binders.push valueBinder) fun xs => do
      let some self := xs.back? | return none
      let some types ← independentFieldTypes fields self | return none
      return some (← types.allM hasLawful)
  let some lawful ← lawfulUnder lawfulBinders | return #[]
  let instBinders? ←
    if lawful then pure (some lawfulBinders)
    else if nonNullBinders.size == lawfulBinders.size then pure none
    else if (← lawfulUnder nonNullBinders) == some true then pure (some nonNullBinders)
    else pure none
  let hyps ← fields.mapM fun field => do
    let f := mkIdent field
    `(bracketedBinderF|($f : _root_.Json.FromJson.fromJson?
        (_root_.Json.ToJson.toJson ($x).$f:ident) = Except.ok ($x).$f:ident))
  let keys ← fields.mapM (jsonFieldName declName)
  -- That no other part carries a field's key is proved part by part, down to the inequality of
  -- two string literals, never by a search through the whole object.
  let distinct (i : Nat) (js : Array Nat) : TermElabM Term := do
    let some (_, key) := keys[i]? | throwError "cannot find the key of field {i} of {declName}"
    js.foldrM (init := ← `(List.forall_mem_nil _)) fun j rest => do
      let some (isOptional, other) := keys[j]? |
        throwError "cannot find the key of field {j} of {declName}"
      let ne ← `(json_keys_ne% $(⟨key⟩) $(⟨other⟩))
      let part ← if isOptional then `(_root_.Json.not_mem_keys_opt $ne)
        else `(_root_.Json.not_mem_keys_single $ne)
      `(List.forall_mem_cons.2 ⟨$part, $rest⟩)
  let lookupNames ← fields.mapM fun _ => return mkIdent (← mkFreshUserName `lookup)
  let lookups ← (fields.zip (keys.zip lookupNames)).mapIdxM
      fun i (field, (isOptional, key), name) => do
    let f := mkIdent field
    let after ← distinct i ((List.range' (i + 1) (fields.size - (i + 1))).toArray)
    -- The parts are found by unifying with the encoding rather than written out again, which for
    -- every field would elaborate every other field's part once more.
    let lemma ←
      if isOptional then
        let before ← distinct i (List.range i).toArray
        `(_root_.Json.getObjValD_mkObj_get_opt (i := $(quote i)) rfl $before $after)
      else
        `(_root_.Json.getObjValD_mkObj_get (i := $(quote i)) rfl $after)
    `(tactic| have $name:ident : (_root_.Json.ToJson.toJson $x).getObjValD $key =
        _root_.Json.ToJson.toJson ($x).$f:ident := $lemma)
  -- A strict decoder's check passes on the encoder's output, which is shown by matching each part
  -- with its key, a step per field that compares no strings.
  let strictCheck ← match ← strictKeys? declName fields with
    | none => pure #[]
    | some (typeName, known) =>
      let keyed ← keys.foldrM (init := ← `(_root_.Json.PartsKeyed.nil)) fun (isOptional, _) rest =>
        if isOptional then `(_root_.Json.PartsKeyed.cons _root_.Json.keyed_opt $rest)
        else `(_root_.Json.PartsKeyed.cons _root_.Json.keyed_single $rest)
      let name := mkIdent (← mkFreshUserName `known)
      pure #[(name, ← `(tactic| have $name:ident : _root_.Json.checkKnownKeys $typeName $known
          (_root_.Json.ToJson.toJson $x) = Except.ok () := _root_.Json.checkKnownKeys_mkObj $keyed))]
  let fromAux := mkIdent (`_root_ ++ fromAux)
  let unfolded ← `(tactic|
    (show $fromAux (_root_.Json.ToJson.toJson $x) = _; unfold $fromAux:ident))
  -- `rw` rather than `simp`: each rule is closed, so one abstraction each finds it under the
  -- decoder's binders, where `simp` would revisit every binder for every rule.
  let rules := strictCheck.map Prod.fst ++ lookupNames ++ fields.map mkIdent
  let rewrite ← if rules.isEmpty then pure #[] else pure #[← `(tactic| rw [$[$rules:term],*])]
  let tactics := strictCheck.map Prod.snd ++ lookups ++ #[unfolded] ++ rewrite ++
    #[← `(tactic| rfl)]
  let name := privateToUserName declName |>.str "fromJson?_toJson"
  let thm := mkIdent (`_root_ ++ name)
  let visibility ← if isPrivateName declName then
      some <$> `(Lean.Parser.Command.visibility| private)
    else pure none
  let thmCmd ← `(
    /-- A value round trips through its derived codec when each of its fields does. -/
    $[$visibility:visibility]? theorem $thm:ident $codecBinders:bracketedBinder* $valueBinder
        $hyps:bracketedBinder* :
        (_root_.Json.FromJson.fromJson? (_root_.Json.ToJson.toJson $x) : Except String $indType) =
          Except.ok $x := by
      $[$tactics:tactic]*)
  let some instBinders := instBinders? | return #[thmCmd]
  let args ← fields.mapM fun _ => `(_root_.Json.LawfulJson.fromJson?_toJson _)
  let instCmd ← `(
    instance $instBinders:bracketedBinder* : _root_.Json.LawfulJson $indType :=
      ⟨fun $x:ident => $thm $x $args*⟩)
  return #[thmCmd, instCmd]

/-! ## The commands -/

open TSyntax.Compat in
private meta def mkToJsonCmds (declName : Name) : TermElabM (Array Command × Ident) := do
  let ctx ← mkContext ``_root_.Json.ToJson "toJson" declName
  let indVal ← theOnlyType ctx declName
  let aux := mkIdent ctx.auxFunNames[0]!
  if let some members ← enumMembers? declName then
    let (pre, post) ← mkEnumToJsonCmds declName members aux
    let instCmds ← mkInstanceCmds ctx ``_root_.Json.ToJson #[declName]
    return (pre ++ instCmds ++ post, aux)
  let header ← mkHeader ``_root_.Json.ToJson 1 indVal
  let binders := header.binders
  let body ← Term.elabBinders binders fun _ => do
    if isStructure (← getEnv) declName then
      mkToJsonBodyForStruct declName aux header
    else
      mkToJsonBodyForInduct indVal aux header
  let auxCmd ← `(def $aux:ident $binders:bracketedBinder* : _root_.Json := $body)
  let instCmds ← mkInstanceCmds ctx ``_root_.Json.ToJson #[declName]
  if !isStructure (← getEnv) declName then return (#[auxCmd] ++ instCmds, aux)
  -- An object, whatever the fields hold, which is what lets an optional field of this type
  -- round trip.
  let argNames ← mkInductArgNames indVal
  let nonNullBinders := (← mkImplicitBinders argNames) ++
    (← mkInstImplicitBinders ``_root_.Json.ToJson indVal argNames)
  let nonNullCmd ← `(instance $nonNullBinders:bracketedBinder* :
      _root_.Json.NonNullJson $(← mkInductiveApp indVal argNames) := ⟨fun _ => nofun⟩)
  return (#[auxCmd] ++ instCmds ++ #[nonNullCmd], aux)

open TSyntax.Compat in
private meta def mkFromJsonCmds (declName : Name) : TermElabM (Array Command × Ident) := do
  let ctx ← mkContext ``_root_.Json.FromJson "fromJson" declName
  let indVal ← theOnlyType ctx declName
  let aux := mkIdent ctx.auxFunNames[0]!
  if let some members ← enumMembers? declName then
    let cmds ← mkEnumFromJsonCmds declName members aux
    let instCmds ← mkInstanceCmds ctx ``_root_.Json.FromJson #[declName]
    return (cmds ++ instCmds, aux)
  let header ← mkHeader ``_root_.Json.FromJson 0 indVal
  -- Only a recursive type needs the count, and computing the depth to seed it is a traversal of
  -- its own, so a decoder that cannot recurse does not carry one.
  let counted := indVal.isRec
  let fuel := mkIdent (← mkFreshUserName `count)
  let json := mkIdent (← mkFreshUserName `json)
  let countBinder ← `(bracketedBinderF|($fuel : Nat))
  let jsonBinder ← `(bracketedBinderF|($json : _root_.Json))
  let binders := if counted then header.binders.push countBinder else header.binders
  let binders := binders.push jsonBinder
  let resultType ← mkInductiveApp indVal header.argNames
  let body ← Term.elabBinders binders fun _ => do
    if isStructure (← getEnv) declName then
      mkFromJsonBodyForStruct declName aux fuel json
    else
      mkFromJsonBodyForInduct indVal aux fuel json
  let exhausted := Lean.quote
    s!"a value nested deeper than the derived decoder for {declName} was prepared to go"
  let auxCmd ←
    if counted then
      `(def $aux:ident $binders:bracketedBinder* : Except String $resultType :=
          match $fuel:ident with
          | 0 => Except.error $exhausted
          | $fuel:ident + 1 => $body)
    else
      `(def $aux:ident $binders:bracketedBinder* : Except String $resultType := $body)
  let argNames ← mkInductArgNames indVal
  let instBinders := (← mkImplicitBinders argNames) ++
    (← mkInstImplicitBinders ``_root_.Json.FromJson indVal argNames)
  let instType ← `(_root_.Json.FromJson $(← mkInductiveApp indVal argNames))
  let instCmd ←
    if counted then
      `(instance $(mkIdent ctx.instName):ident $instBinders:bracketedBinder* : $instType :=
          ⟨fun j => $aux (_root_.Json.depth j + 1) j⟩)
    else
      `(instance $(mkIdent ctx.instName):ident $instBinders:bracketedBinder* : $instType :=
          ⟨$aux⟩)
  return (#[auxCmd, instCmd], aux)

/--
Records the function a handler defined, and adds the round trip if the other codec was derived
already.
-/
private meta def addRoundTrip (cls declName : Name) (aux : Ident) : CommandElabM Unit := do
  let aux ← resolveGlobalConstNoOverload aux
  modifyEnv (derivedCodecs.addEntry · (cls, declName, aux))
  let env ← getEnv
  if let some fromAux := derivedCodec? env ``_root_.Json.FromJson declName then
    if (derivedCodec? env ``_root_.Json.ToJson declName).isSome then
      (← liftTermElabM <| mkRoundTripCmds declName fromAux).forM elabCommand

private meta def recordIfEnum (declName : Name) : CommandElabM Unit := do
  if let some members ← liftTermElabM <| enumMembers? declName then
    recordEnum declName members

meta def toJsonHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 && (← isInductive declNames[0]!) then
    let (cmds, aux) ← liftTermElabM <| mkToJsonCmds declNames[0]!
    cmds.forM elabCommand
    recordIfEnum declNames[0]!
    addRoundTrip ``_root_.Json.ToJson declNames[0]! aux
    return true
  else
    return false

meta def fromJsonHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 && (← isInductive declNames[0]!) then
    let (cmds, aux) ← liftTermElabM <| mkFromJsonCmds declNames[0]!
    cmds.forM elabCommand
    recordIfEnum declNames[0]!
    addRoundTrip ``_root_.Json.FromJson declNames[0]! aux
    return true
  else
    return false

meta initialize
  registerDerivingHandler ``_root_.Json.ToJson toJsonHandler
  registerDerivingHandler ``_root_.Json.FromJson fromJsonHandler

end Json.Deriving
