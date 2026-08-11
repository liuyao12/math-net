import Lean
import MathNetwork.Fermat.Registry
import MathNetwork.Euler.Applications

/-! A small, environment-based declaration dependency extractor. -/

open Lean Elab Command


private def namesToJson (xs : Array Name) : Json :=
  toJson (xs.map Name.toString)

private def directConstants (ci : ConstantInfo) : Array Name :=
  let used := ci.type.getUsedConstantsAsSet.toArray.foldl
    (init := ({} : NameSet)) fun used name => NameSet.insert used name
  let used := match ci.value? (allowOpaque := true) with
    | some value => value.getUsedConstantsAsSet.toArray.foldl
        (init := used) fun used name => NameSet.insert used name
    | none => used
  used.toArray.qsort Name.lt

private def graphRelevant (name : Name) : Bool :=
  let text := name.toString
  text.startsWith "MathNetwork." ||
    text.startsWith "ComputableAnalysis." ||
    text.startsWith "Complex." ||
    text.startsWith "Real."

private def graphConstants (ci : ConstantInfo) : Array Name :=
  (directConstants ci).filter graphRelevant

private partial def transitiveConstants (env : Environment) (roots : Array Name) : Array Name :=
  let rec visit (todo : Array Name) (seen : NameSet) : NameSet :=
    if let some name := todo[0]? then
      let todo := todo.extract 1 todo.size
      if seen.contains name then visit todo seen
      else
        let seen := seen.insert name
        match env.find? name with
        | some ci => visit (todo ++ directConstants ci) seen
        | none => visit todo seen
    else seen
  (visit roots {}).toArray.qsort Name.lt

private partial def stringLiterals (e : Expr) : Array String :=
  match e with
  | .lit (.strVal value) => #[value]
  | .app f a => stringLiterals f ++ stringLiterals a
  | .lam _ type body _ => stringLiterals type ++ stringLiterals body
  | .forallE _ type body _ => stringLiterals type ++ stringLiterals body
  | .letE _ type value body _ => stringLiterals type ++ stringLiterals value ++ stringLiterals body
  | .mdata _ body => stringLiterals body
  | .proj _ _ body => stringLiterals body
  | _ => #[]

private def routeMetadata (ci : ConstantInfo) : Json :=
  let (fn, args) := ci.type.getAppFnArgs
  if fn == ``MathNetwork.Fermat.ProofRoute && args.size >= 1 then
    let strings := (ci.value? (allowOpaque := true)).map stringLiterals |>.getD #[]
    let routeName := strings[0]?.getD ""
    let routeDescription := strings[1]?.getD ""
    Json.mkObj [
      ("kind", "ProofRoute"),
      ("target_type", toString args[0]!),
      ("name", routeName),
      ("description", routeDescription),
      ("metadata_source", "ProofRoute declaration value"),
      ("proof_field", "included in direct_constants")
    ]
  else Json.null

private def declarationJson (env : Environment) (name : Name) : CommandElabM Json := do
  let some ci := env.find? name | throwError s!"declaration not found: {name}"
  let direct := (directConstants ci).filter (· != name)
  let graphDirect := (graphConstants ci).filter (· != name)
  let transitive := (transitiveConstants env #[name]).filter (· != name)
  let axioms ← Lean.collectAxioms name
  return Json.mkObj [
    ("declaration", name.toString),
    ("module", match env.getModuleIdxFor? name with
      | some (i : ModuleIdx) => env.header.moduleNames[i.toNat]!.toString
      | none => env.mainModule.toString),
    ("direct_constants", namesToJson direct),
    ("graph_direct_constants", namesToJson graphDirect),
    ("transitive_constants", namesToJson transitive),
    ("axioms", namesToJson axioms),
    ("proof_route", routeMetadata ci)
  ]

private def declarationNames (raw : String) : Except String (Array Name) := do
  if raw.isEmpty then Except.error "missing MATHNET_DECLARATIONS=Name[,Name,...]"
  else
    let parts := raw.splitOn ","
    let names ← parts.mapM fun name =>
      let name := name.trimAscii
      if name.isEmpty then Except.error "empty declaration name"
      else Except.ok name.toName
    Except.ok names.toArray

syntax "extract_deps" : command

elab_rules : command
  | `(extract_deps) => do
    let env ← getEnv
    let some raw ← liftIO <| IO.getEnv "MATHNET_DECLARATIONS"
      | throwError "missing MATHNET_DECLARATIONS=Name[,Name,...]"
    let names ← match declarationNames raw with
      | .ok names => pure names
      | .error msg => throwError msg
    let values ← names.mapM (declarationJson env)
    let report := Json.mkObj [
      ("schema_version", "0.1"),
      ("main_module", env.mainModule.toString),
      ("imports", toJson (env.imports.map (·.module.toString))),
      ("declarations", toJson values)
    ]
    liftIO <| IO.println report.compress

extract_deps
