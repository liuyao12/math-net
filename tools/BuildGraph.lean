import Lean
import MathNetwork.Fermat.Registry
import MathNetwork.Euler.Applications

/-!
# Build the project-wide declaration graph

This intentionally works from the elaborated Lean environment. User-facing
project theorems become proposition nodes, definitions become concept nodes,
and their direct constants defined in mathlib become imported source nodes.
Every edge is therefore a strict
`used-in-proof` edge; this is a declaration graph, not a hand-curated theorem
relationship graph.
-/

open Lean Elab Command

private def isProject (name : Name) : Bool :=
  name.toString.startsWith "MathNetwork."

private def isInternal (name : Name) : Bool :=
  let text := name.toString
  name.isInternalDetail || text.startsWith "_" || text.contains "._proof_" ||
    text.contains ".inst" || text.contains ".mk.inj" || text.contains ".recOn" ||
    text.contains ".noConfusion" || text.contains ".ctorIdx" ||
    text.contains ".sizeOf_spec" || text.contains ".eq_"

private def shortName (name : Name) : String :=
  name.toString.splitOn "." |>.getLastD name.toString

private def declarationKind (ci : ConstantInfo) : String × String :=
  match ci with
  | .thmInfo _ => ("proposition", "theorem")
  | .opaqueInfo _ => ("proposition", "theorem")
  | .axiomInfo _ => ("proposition", "conjecture")
  | .defnInfo _ => ("concept", "definition")
  | .quotInfo _ => ("concept", "definition")
  | .inductInfo _ => ("concept", "definition")
  | .ctorInfo _ => ("concept", "definition")
  | .recInfo _ => ("concept", "definition")

private def moduleOf (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some (i : ModuleIdx) => env.header.moduleNames[i.toNat]!.toString
  | none => ""

private def isMathlibDependency (env : Environment) (name : Name) : Bool :=
  (moduleOf env name).startsWith "Mathlib."

private def directConstants (ci : ConstantInfo) : Array Name :=
  ci.getUsedConstantsAsSet.toArray.qsort Name.lt

private def indexOf (name : Name) (names : Array Name) : Nat :=
  let rec go (xs : List Name) (i : Nat) : Nat :=
    match xs with
    | [] => 0
    | x :: rest => if x == name then i else go rest (i + 1)
  go names.toList 0

private def projectNames (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun names name _ =>
    if isProject name && !isInternal name then names.push name else names

private def dependencyNames (env : Environment) (targets : Array Name) : Array Name :=
  (targets.foldl (init := ({} : NameSet)) fun names target =>
    match env.find? target with
    | some ci =>
      (directConstants ci).foldl (init := names) fun names dependency =>
        if isMathlibDependency env dependency && !isInternal dependency then
          names.insert dependency
        else names
    | none => names).toArray.qsort Name.lt

private def projectNode (env : Environment) (ci : ConstantInfo) (name : Name) (index : Nat) : Json :=
  let (kind, role) := declarationKind ci
  Json.mkObj [
    ("id", s!"decl-{index}"),
    ("kind", kind),
    ("role", role),
    ("label", shortName name),
    ("statement", toString ci.type),
    ("namespace", name.toString),
    ("module", moduleOf env name),
    ("formalizations", Json.arr #[Json.mkObj [
      ("language", "Lean"),
      ("name", name.toString)
    ]]),
    ("verification", Json.mkObj [
      ("state", "checked"),
      ("scope", "local-with-imports"),
      ("closure", "partial"),
      ("note", "Generated from the elaborated project environment; direct mathlib dependencies are shown as imported source nodes.")
    ])
  ]

private def dependencyNode (name : Name) (index : Nat) (module : String) : Json :=
  Json.mkObj [
    ("id", s!"const-{index}"),
    ("kind", "source"),
    ("label", shortName name),
    ("namespace", name.toString),
    ("locator", s!"mathlib/{module}"),
    ("citation", name.toString),
    ("verification", Json.mkObj [
      ("state", "imported-checked"),
      ("scope", "imported"),
      ("closure", "closed")
    ])
  ]

private def dependencyEdges (env : Environment) (targets dependencies : Array Name) : Array Json :=
  targets.foldl (init := #[]) fun edges target =>
    match env.find? target with
    | some ci =>
      let (targetKind, _) := declarationKind ci
      if targetKind != "proposition" then edges else
      (directConstants ci).foldl (init := edges) fun edges dependency =>
        if dependencies.contains dependency then
          let targetIndex := indexOf target targets
          let dependencyIndex := indexOf dependency dependencies
          edges.push <| Json.mkObj [
            ("id", s!"use-{targetIndex}-{dependencyIndex}"),
            ("relation", "used-in-proof"),
            ("proof", s!"decl-{targetIndex}"),
            ("source", Json.mkObj [("id", s!"const-{dependencyIndex}"), ("kind", "source")]),
            ("target", Json.mkObj [("id", s!"decl-{targetIndex}"), ("kind", "proposition")]),
            ("description", s!"{dependency} is a direct Lean dependency of {target}.")
          ]
        else if targets.contains dependency then
          let targetIndex := indexOf target targets
          let dependencyIndex := indexOf dependency targets
          let sourceKind := match env.find? dependency with
            | some sourceInfo => (declarationKind sourceInfo).1
            | none => "proposition"
          edges.push <| Json.mkObj [
            ("id", s!"local-use-{targetIndex}-{dependencyIndex}"),
            ("relation", "used-in-proof"),
            ("proof", s!"decl-{targetIndex}"),
            ("source", Json.mkObj [("id", s!"decl-{dependencyIndex}"), ("kind", sourceKind)]),
            ("target", Json.mkObj [("id", s!"decl-{targetIndex}"), ("kind", "proposition")]),
            ("description", s!"{dependency} is a direct Lean dependency of {target}.")
          ]
        else edges
    | none => edges

syntax "build_project_graph" : command

elab_rules : command
  | `(build_project_graph) => do
    let env ← getEnv
    let targets := projectNames env
    let dependencies := dependencyNames env targets
    let nodes := targets.mapIdx (fun i name =>
      match env.find? name with
      | some ci => projectNode env ci name i
      | none => Json.mkObj [("id", s!"decl-{i}"), ("kind", "proposition"),
          ("role", "theorem"), ("label", shortName name),
          ("statement", s!"Lean declaration {name}")]) ++
      dependencies.mapIdx (fun i name => dependencyNode name i (moduleOf env name))
    let edges := dependencyEdges env targets dependencies
    let report := Json.mkObj [
      ("schemaVersion", "1.0"),
      ("graphId", "math-net-project-declarations"),
      ("label", "math-net: Lean declaration dependencies"),
      ("nodes", toJson nodes),
      ("edges", toJson edges)
    ]
    liftIO <| IO.println report.compress

build_project_graph
