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
  let key :=
    match naming.overrides.find? (·.1 == n) with
    | some (_, key) => key
    | none =>
      match naming.convention with
      | some convention => convention.apply stripped
      | none => stripped
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

/-! ## The commands -/

open TSyntax.Compat in
private meta def mkToJsonCmds (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext ``_root_.Json.ToJson "toJson" declName
  let indVal ← theOnlyType ctx declName
  let aux := mkIdent ctx.auxFunNames[0]!
  let header ← mkHeader ``_root_.Json.ToJson 1 indVal
  let binders := header.binders
  let body ← Term.elabBinders binders fun _ => do
    if isStructure (← getEnv) declName then
      mkToJsonBodyForStruct declName aux header
    else
      mkToJsonBodyForInduct indVal aux header
  let auxCmd ← `(def $aux:ident $binders:bracketedBinder* : _root_.Json := $body)
  return #[auxCmd] ++ (← mkInstanceCmds ctx ``_root_.Json.ToJson #[declName])

open TSyntax.Compat in
private meta def mkFromJsonCmds (declName : Name) : TermElabM (Array Command) := do
  let ctx ← mkContext ``_root_.Json.FromJson "fromJson" declName
  let indVal ← theOnlyType ctx declName
  let aux := mkIdent ctx.auxFunNames[0]!
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
  return #[auxCmd, instCmd]

meta def toJsonHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 && (← isInductive declNames[0]!) then
    (← liftTermElabM <| mkToJsonCmds declNames[0]!).forM elabCommand
    return true
  else
    return false

meta def fromJsonHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.size == 1 && (← isInductive declNames[0]!) then
    (← liftTermElabM <| mkFromJsonCmds declNames[0]!).forM elabCommand
    return true
  else
    return false

meta initialize
  registerDerivingHandler ``_root_.Json.ToJson toJsonHandler
  registerDerivingHandler ``_root_.Json.FromJson fromJsonHandler

end Json.Deriving
