import Lean
import Std.Data.HashMap.Basic

open Lean
open Std (HashMap)

/-!
# `lean4_export.lean` — Official `lean4export` `3.1.0` Multi-Version Exporter
Supports both `v4.33.1` (pinned Mettapedia/Mathlib) and `v4.35.0` (latest stable Lean 4),
emitting exact `lean4export` `3.1.0` NDJSON format for `tcalc/lean_tcalc.c`.
-/

def Lean.BinderInfo.toJson : BinderInfo → Json
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def Lean.ReducibilityHints.toJson : ReducibilityHints → Json
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular n => .mkObj [("regular", n.toNat)]

def Lean.QuotKind.toJson : QuotKind → Json
  | .type => "type"
  | .ctor => "ctor"
  | .lift => "lift"
  | .ind => "ind"

def Lean.DefinitionSafety.toJson : DefinitionSafety → Json
  | .unsafe => "unsafe"
  | .safe => "safe"
  | .partial => "partial"

def Lean.KVMap.toJson (kvs : Lean.KVMap) : Json :=
  .mkObj <| kvs.entries.map (fun (k, v) => (k.toString, reprStr v))

structure Context where
  env : Environment

structure State where
  visitedNames : HashMap Name Nat := HashMap.emptyWithCapacity 200000 |>.insert .anonymous 0
  visitedLevels : HashMap Level Nat := HashMap.emptyWithCapacity 1000 |>.insert .zero 0
  visitedExprs : HashMap Expr Nat := HashMap.emptyWithCapacity 1000000
  visitedConstants : NameHashSet := {}
  noMDataExprs : HashMap Expr Expr := HashMap.emptyWithCapacity 100000
  exportMData : Bool := false
  exportUnsafe : Bool := false
  ignoreMissing : Bool := false
  recursorMap : NameMap NameSet := {}

abbrev M := ReaderT Context <| StateT State IO

def M.run (env : Environment) (act : M α) : IO α :=
  StateT.run' (s := {}) do
    ReaderT.run (r := { env }) do
      act

def initState (env : Environment) (cliOptions : List String := []) : M Unit := do
  let mut recursorMap : NameMap NameSet := {}
  for (_, constInfo) in env.constants do
    if let .recInfo recVal := constInfo then
      for indName in recVal.all do
        recursorMap := recursorMap.alter indName <|
          fun
          | none => some <| NameSet.empty.insert recVal.name
          | some recNames => some <| recNames.insert recVal.name
  modify fun st => { st with
    exportMData   := cliOptions.any (· == "--export-mdata")
    exportUnsafe  := cliOptions.any (· == "--export-unsafe")
    ignoreMissing := cliOptions.any (· == "--ignore-missing")
    recursorMap
  }

@[inline]
def getIdx [Hashable α] [BEq α] (x : α) (namespaced : String)
    (getM : State → HashMap α Nat) (setM : State → HashMap α Nat → State) (rec : M Json) : M Nat := do
  let m ← getM <$> get
  if let some idx := m[x]? then
    return idx
  let s ← rec
  let m ← getM <$> get
  let idx := m.size
  IO.println (s.setObjVal! namespaced idx).compress
  modify fun st => setM st ((getM st).insert x idx)
  return idx

def dumpName (n : Name) : M Nat := getIdx n "in" (·.visitedNames) ({ · with visitedNames := · }) do
  match n with
  | .anonymous => throw <| IO.userError "anonymous name must be index 0"
  | .str n s =>
    return .mkObj [
      ("str", .mkObj [
        ("pre", ← dumpName n),
        ("str", s)
      ])
    ]
  | .num n i =>
    return .mkObj [
      ("num", .mkObj [
        ("pre", ← dumpName n),
        ("i", i)
      ])
    ]

def dumpLevel (l : Level) : M Nat := getIdx l "il" (·.visitedLevels) ({ · with visitedLevels := · }) do
  match l with
  | .zero => throw <| IO.userError "zero level must be index 0"
  | .mvar _ => throw <| IO.userError "cannot export universe level metavariable"
  | .succ l => return .mkObj [("succ", ← dumpLevel l)]
  | .max l1 l2 => return .mkObj [("max", Json.arr #[← dumpLevel l1, ← dumpLevel l2])]
  | .imax l1 l2 => return .mkObj [("imax", Json.arr #[← dumpLevel l1, ← dumpLevel l2])]
  | .param n => return .mkObj [("param", ← dumpName n)]

def dumpUparams (uparams : List Name) : M Json := do
  let nameIdxs ← uparams.mapM dumpName
  let _ ← (uparams.map Level.param).mapM dumpLevel
  pure nameIdxs.toJson

def dumpNames (uparams : List Name) : M Json := do
  let nameIdxs ← uparams.mapM dumpName
  return nameIdxs.toJson

def removeMData (e : Expr) : M Expr := do
  if let some x := (← get).noMDataExprs[e]? then
    return x
  let e' ← match e with
  | .mdata _ e' => removeMData e'
  | .fvar .. | .mvar .. => throw <| IO.userError "cannot export free variables or metavariables"
  | .bvar .. | .sort .. | .const .. | .lit _ => pure e
  | .app f a =>
    pure <| e.updateApp! (← removeMData f) (← removeMData a)
  | .lam _ d b _ =>
    pure <| e.updateLambdaE! (← removeMData d) (← removeMData b)
  | .letE _ d v b _ =>
    pure <| e.updateLet! (← removeMData d) (← removeMData v) (← removeMData b) false
  | .forallE _ d b _ =>
    pure <| e.updateForallE! (← removeMData d) (← removeMData b)
  | .proj _ _ e2 =>
    pure <| e.updateProj! (← removeMData e2)
  modify (fun st => { st with noMDataExprs := st.noMDataExprs.insert e e' })
  pure e'

mutual

partial def dumpExprAux (e : Expr) : M Nat := do
  getIdx e "ie" (·.visitedExprs) ({ · with visitedExprs := · }) do
    match e with
    | .fvar .. | .mvar .. => throw <| IO.userError "cannot export free variables or metavariables"
    | .mdata a e' =>
      return .mkObj [
        ("mdata", .mkObj [
            ("data", a.toJson),
            ("expr", ← dumpExprAux e')
        ])
      ]
    | .bvar i => return .mkObj [("bvar", i)]
    | .lit (.natVal i) => dumpNatDeps; return .mkObj [("natVal", s!"{i}")]
    | .lit (.strVal s) => dumpStrDeps; return .mkObj [("strVal", s)]
    | .sort l => return .mkObj [("sort", ← dumpLevel l)]
    | .const n us => return .mkObj [
      ("const", .mkObj [
        ("name", ← dumpName n),
        ("us", (← us.mapM dumpLevel).toJson)
      ])
    ]
    | .app f a => return .mkObj [
      ("app", .mkObj [
        ("fn", ← dumpExprAux f),
        ("arg", ← dumpExprAux a)
      ])
    ]
    | .lam n d b bi => return .mkObj [
      ("lam", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("body", ← dumpExprAux b),
        ("binderInfo", bi.toJson)
      ])
    ]
    | .forallE n d b bi => return .mkObj [
      ("forallE", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("body", ← dumpExprAux b),
        ("binderInfo", bi.toJson)
      ])
    ]
    | .letE n d v b nondep => return .mkObj [
      ("letE", .mkObj [
        ("name", ← dumpName n),
        ("type", ← dumpExprAux d),
        ("value", ← dumpExprAux v),
        ("body", ← dumpExprAux b),
        ("nondep", nondep)
      ])
    ]
    | .proj s i e => return .mkObj [
      ("proj", .mkObj [
        ("typeName", ← dumpName s),
        ("idx", i),
        ("struct", ← dumpExprAux e)
      ])
    ]
where
  dumpNatDeps : M Unit := do
    let nat := ``Nat
    if (!(← get).visitedConstants.contains nat) && ((← read).env.find? nat).isSome
    then dumpConstant nat
  dumpStrDeps : M Unit := do
    let charOfNat := ``Char.ofNat
    if (!(← get).visitedConstants.contains charOfNat) && ((← read).env.find? charOfNat).isSome
    then dumpConstant charOfNat
    let stringOfList := ``String.ofList
    if (!(← get).visitedConstants.contains stringOfList) && ((← read).env.find? stringOfList).isSome
    then dumpConstant stringOfList

partial def dumpExpr (e : Expr) : M Nat := do
  let aux (e : Expr) : M Expr := do
    modify (fun st => { st with noMDataExprs := HashMap.emptyWithCapacity 1024 })
    removeMData e
  dumpExprAux <| ← if (← get).exportMData then pure e else aux e

partial def dumpConstant (c : Name) : M Unit := do
  let some declar := (← read).env.find? c
    | if (← get).ignoreMissing then return else throw <| IO.userError s!"Constant {c} not found in environment."
  if ((declar.isUnsafe || declar.isPartial) && !(← get).exportUnsafe) || (← get).visitedConstants.contains c then
    return
  modify fun st => { st with visitedConstants := st.visitedConstants.insert c }
  match declar with
  | .axiomInfo val => do
    dumpDeps val.type
    dumpObj [
      ("axiom", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("isUnsafe", val.isUnsafe)
      ])
    ]
  | .defnInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("def", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("hints", val.hints.toJson),
        ("safety", val.safety.toJson),
        ("all", ← dumpNames val.all)
      ])
    ]
  | .opaqueInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("opaque", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("all", ← dumpNames val.all),
        ("isUnsafe", val.isUnsafe)
      ])
    ]
  | .thmInfo val => do
    dumpDeps val.type
    dumpDeps val.value
    dumpObj [
      ("thm", Json.mkObj [
        ("name", ← dumpName val.name),
        ("levelParams", ← dumpUparams val.levelParams),
        ("type", ← dumpExpr val.type),
        ("value", ← dumpExpr val.value),
        ("all", ← dumpNames val.all)
      ])
    ]
  | .quotInfo _ =>
    dumpConstant ``Eq
    for qc in [`Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      let some (.quotInfo val) := (← read).env.find? qc
        | if (← get).ignoreMissing then return else throw <| IO.userError s!"Constant {qc} not found in environment."
      modify fun st => { st with visitedConstants := st.visitedConstants.insert qc }
      dumpDeps val.type
      dumpObj [
        ("quot", .mkObj [
          ("name", ← dumpName val.name),
          ("levelParams", ← dumpUparams val.levelParams),
          ("type", ← dumpExpr val.type),
          ("kind", val.kind.toJson)
        ])
      ]
  | .inductInfo baseIndVal => do
    let mut indVals := #[]
    let mut ctorVals := #[]
    let mut recursorNames := NameSet.empty
    for indName in baseIndVal.all do
      let some (.inductInfo val) := (← read).env.find? indName
        | throw <| IO.userError s!"Expected inductive {indName}"
      if val.isUnsafe && !(← get).exportUnsafe then return
      indVals := indVals.push val
      for ctor in val.ctors do
        match (← read).env.find? ctor with
        | some (.ctorInfo ctorVal) =>
          if ctorVal.isUnsafe && !(← get).exportUnsafe then return
          ctorVals := ctorVals.push ctorVal
        | _ => throw <| IO.userError s!"Expected a ConstantInfo.ctorInfo for {ctor}."
      modify fun st => { st with visitedConstants := st.visitedConstants.insert indName }
      dumpDeps val.type
      if let .some names := (← get).recursorMap.get? indName then
        recursorNames := recursorNames.union names

    for ctorVal in ctorVals do
      modify fun st => { st with visitedConstants := st.visitedConstants.insert ctorVal.name }
      dumpDeps ctorVal.type

    let mut recursorVals := #[]
    for recursorName in recursorNames do
      match (← read).env.find? recursorName with
      | some (.recInfo recVal) =>
        if !recVal.isUnsafe || (← get).exportUnsafe then
          recursorVals := recursorVals.push recVal
      | _ => throw <| IO.userError s!"Expected a ConstantInfo.recInfo for {recursorName}."
    for recursorVal in recursorVals do
      modify fun st => { st with visitedConstants := st.visitedConstants.insert recursorVal.name }
      dumpDeps recursorVal.type

    for recursorVal in recursorVals do
      for rule in recursorVal.rules do
        dumpDeps rule.rhs

    let inductiveValsJson ← indVals.mapM <| fun indVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName indVal.name),
          ("levelParams", ← dumpUparams indVal.levelParams),
          ("type", ← dumpExpr indVal.type),
          ("numParams", indVal.numParams),
          ("numIndices", indVal.numIndices),
          ("all", ← dumpNames indVal.all),
          ("ctors", ← dumpNames indVal.ctors),
          ("numNested", indVal.numNested),
          ("isRec", indVal.isRec),
          ("isReflexive", indVal.isReflexive),
          ("isUnsafe", indVal.isUnsafe)
      ]
    let ctorValsJson ← ctorVals.mapM <| fun ctorVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName ctorVal.name),
          ("levelParams", ← dumpUparams ctorVal.levelParams),
          ("type", ← dumpExpr ctorVal.type),
          ("induct", ← dumpName ctorVal.induct),
          ("cidx", ctorVal.cidx),
          ("numParams", ctorVal.numParams),
          ("numFields", ctorVal.numFields),
          ("isUnsafe", ctorVal.isUnsafe)
      ]
    let recursorValsJson ← recursorVals.mapM <| fun recursorVal => do
      pure <| Json.mkObj [
          ("name", ← dumpName recursorVal.name),
          ("levelParams", ← dumpUparams recursorVal.levelParams),
          ("type", ← dumpExpr recursorVal.type),
          ("all", ← dumpNames recursorVal.all),
          ("numParams", recursorVal.numParams),
          ("numIndices", recursorVal.numIndices),
          ("numMotives", recursorVal.numMotives),
          ("numMinors", recursorVal.numMinors),
          ("rules", (← recursorVal.rules.mapM dumpRecRule).toJson),
          ("k", recursorVal.k),
          ("isUnsafe", recursorVal.isUnsafe)
      ]
    dumpObj [
      ("inductive", Json.mkObj [
        ("types", inductiveValsJson.toJson),
        ("ctors", ctorValsJson.toJson),
        ("recs", recursorValsJson.toJson)
      ])
    ]
  | .ctorInfo val => dumpConstant val.induct
  | .recInfo val =>
    for indName in val.all do
      dumpConstant indName
where
  dumpDeps e := do
    for c in e.getUsedConstants do
      dumpConstant c
  dumpRecRule (rule : RecursorRule) : M Json := do
    return Json.mkObj [
      ("ctor", ← dumpName rule.ctor),
      ("nfields", rule.nfields),
      ("rhs", ← dumpExpr rule.rhs)
    ]
  dumpObj (fields : List (String × Json)) : M Unit :=
    IO.println <| Json.mkObj fields |>.compress

end

def exportMetadata : Json :=
  let leanMeta := Json.mkObj [
    ("version", versionString),
    ("githash", githash)
  ]
  let exporterMeta := Json.mkObj [
    ("name", "lean4export"),
    ("version", "3.1.0")
  ]
  let formatMeta := Json.mkObj [
    ("version", "3.1.0")
  ]
  Json.mkObj [
    ("meta", Json.mkObj [
      ("exporter", exporterMeta),
      ("lean", leanMeta),
      ("format", formatMeta)
    ])
  ]

def dumpMetadata : M Unit := do
  IO.println exportMetadata.compress

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let (opts, posArgs) := args.partition (fun s => s.startsWith "--" && s.length ≥ 3)
  let moduleOnly := opts.any (fun s => s == "--module-only" || s == "--closure")
  let emitManifestOpt := opts.findSome? (fun s =>
    if s.startsWith "--emit-manifest=" then some (System.FilePath.mk (s.drop 16).toString) else none)
  let (importStrs, constStrs) :=
    if posArgs.any (· == "--") then
      let (im, rest) := posArgs.span (· != "--")
      (im, rest.drop 1)
    else if moduleOnly then
      (posArgs, [])
    else
      match posArgs with
      | [] => (["Init.Core"], [])
      | [m] => ([m], [])
      | m :: cs => ([m], cs)
  let imports := importStrs.toArray.map fun mod => { module := mod.toName }
  let env ← importModules imports {} 0
  let constants : List Name ←
    if !constStrs.isEmpty then
      pure <| constStrs.map String.toName
    else if moduleOnly then
      let mut modConsts : Array Name := #[]
      for modStr in importStrs do
        let modNm := modStr.toName
        if let some modIdx := env.header.moduleNames.idxOf? modNm then
          if h : modIdx < env.header.moduleData.size then
            for nm in env.header.moduleData[modIdx].constNames do
              if !nm.isInternal then
                modConsts := modConsts.push nm
      pure modConsts.toList
    else
      pure <| env.constants.toList.map Prod.fst |>.filter (!·.isInternal)
  M.run env do
    let _ ← initState env opts
    dumpMetadata
    for c in constants do
      modify (fun st => { st with noMDataExprs := {} })
      dumpConstant c
    if let some mpath := emitManifestOpt then
      let visited := (← get).visitedConstants
      let mut lines : Array String := #["# Lean 4 Kernel Declaration Inventory Manifest"]
      for c in constants do
        if visited.contains c then
          lines := lines.push (c.toString (escape := false))
      IO.FS.writeFile mpath (String.intercalate "\n" lines.toList ++ "\n")
