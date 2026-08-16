import Lean

/-!
# Build the project-wide declaration graph

This intentionally works from the elaborated Lean environment. User-facing
project declarations and imported constants retain their actual Lean
declaration kind (`theorem`, `definition`, `axiom`, and so on). The imported
closure is expanded to a bounded depth so a selected theorem has multiple
visible layers of dependencies. Every edge is therefore a strict
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
  | .thmInfo _ => ("theorem", "theorem")
  | .opaqueInfo _ => ("opaque", "opaque")
  | .axiomInfo _ => ("axiom", "axiom")
  | .defnInfo _ => ("definition", "definition")
  | .quotInfo _ => ("quotient", "definition")
  | .inductInfo _ => ("inductive", "inductive")
  | .ctorInfo _ => ("constructor", "constructor")
  | .recInfo _ => ("recursor", "recursor")

private def graphKind (ci : ConstantInfo) : String :=
  let (kind, _) := declarationKind ci
  if kind == "theorem" || kind == "opaque" || kind == "axiom" then "proposition" else "concept"

private def moduleOf (env : Environment) (name : Name) : String :=
  match env.getModuleIdxFor? name with
  | some (i : ModuleIdx) => env.header.moduleNames[i.toNat]!.toString
  | none => ""

private def isTrackedDependency (env : Environment) (name : Name) : Bool :=
  let module := moduleOf env name
  module.startsWith "Mathlib." || module.startsWith "ComputableAnalysis."

/-! Domain slices deliberately collect one extra layer. `CombineRawGraphs.py`
then computes the original three-layer closure from the union of all project
targets. The overlap removes import-order artefacts at a slice boundary. -/
private def maxDependencyDepth : Nat := 4

private def bodyConstants (ci : ConstantInfo) : Array Name :=
  /- A declaration's type is its *statement*, not evidence that the listed
  constants were used to establish it.  In particular, `sqrt`, `Irrational`,
  and `IsSquare` occur in the type of the square-root criterion, but showing
  them as arrows into the theorem confuses its vocabulary with its proof.

  The landscape therefore follows constants in the elaborated declaration
  body only.  For a theorem this is its checked proof term; for a definition
  it is its checked implementation.  Axioms and opaque imported declarations
  without an inspectable body become honest boundary nodes rather than
  receiving invented statement-reference arrows.
  -/
  match ci.value? (allowOpaque := true) with
  | some value =>
    -- Proof terms are lambdas over the theorem's binders.  Lean therefore
    -- stores the binder types inside `value` as well.  Remove every constant
    -- already present in `ci.type`: those name the proposition being proved,
    -- not a fact used to prove it.  What remains is the proof-specific body
    -- dependency set.
    let statementConstants := ci.type.getUsedConstantsAsSet
    value.getUsedConstantsAsSet.toArray
      |>.filter (fun name => !statementConstants.contains name)
      |>.qsort Name.lt
  | none => #[]

private def indexOf (name : Name) (names : Array Name) : Nat :=
  let rec go (xs : List Name) (i : Nat) : Nat :=
    match xs with
    | [] => 0
    | x :: rest => if x == name then i else go rest (i + 1)
  go names.toList 0

private def projectNames (env : Environment) : Array Name :=
  env.constants.fold (init := #[]) fun names name _ =>
    if isProject name && !isInternal name then names.push name else names

private def dependencyDepths (env : Environment) (targets : Array Name) : Array (Name × Nat) :=
  let rec visit (fuel : Nat) (frontier : Array (Name × Nat)) (seen : NameSet) (out : Array (Name × Nat)) : Array (Name × Nat) :=
    match fuel with
    | 0 => out
    | fuel + 1 =>
      match frontier.toList with
      | [] => out
      | (name, depth) :: rest =>
        let seen := seen.insert name
        let out := if isTrackedDependency env name && !isInternal name then out.push (name, depth) else out
        if depth >= maxDependencyDepth then visit fuel rest.toArray seen out
        else
          match env.find? name with
          | some ci =>
            let (next, seen) := (bodyConstants ci).foldl
              (init := (rest.toArray, seen)) fun (next, seen) dependency =>
                if isTrackedDependency env dependency && !isInternal dependency &&
                    !seen.contains dependency then
                  (next.push (dependency, depth + 1), seen.insert dependency)
                else (next, seen)
            visit fuel next seen out
          | none => visit fuel rest.toArray seen out
  -- Targets are the initial work items and must still be processed; later
  -- discoveries are inserted into `seen` when enqueued to avoid the large
  -- duplicate frontier that made the original extractor appear to hang.
  visit 100000 (targets.map (fun name => (name, 0))) {} #[]

private def dependencyNames (env : Environment) (targets : Array Name) : Array Name :=
  (dependencyDepths env targets).map (·.1) |>.qsort Name.lt

private def structuralProjectionNames (env : Environment) (included : Array Name) : NameSet :=
  /- Scanning all Mathlib declarations here is needlessly expensive: the
  graph contains only project declarations and their bounded dependency
  closure.  Restricting the structural-metadata pass to that closure keeps
  the extractor usable on a standard CI runner without changing any node or
  edge that can appear in the graph. -/
  included.foldl (init := ({} : NameSet)) fun names name =>
    if (env.getProjectionFnInfo? name).isSome then names.insert name else names

private def projectNode (env : Environment) (projections : NameSet) (ci : ConstantInfo) (name : Name) (index : Nat) : Json :=
  let (declarationKind, rawRole) := declarationKind ci
  let role := if isStructure env name then "structure" else rawRole
  Json.mkObj [
    ("id", s!"decl-{index}"),
    ("kind", graphKind ci),
    ("declarationKind", declarationKind),
    ("role", role),
    ("label", shortName name),
    ("statement", toString ci.type),
    ("namespace", name.toString),
    ("structuralProjection", Json.bool (projections.contains name)),
    ("module", moduleOf env name),
    ("formalizations", Json.arr #[Json.mkObj [
      ("language", "Lean"),
      ("name", name.toString)
    ]]),
    ("verification", Json.mkObj [
      ("state", "checked"),
      ("scope", "local-with-imports"),
      ("closure", "partial"),
      ("note", "Generated from the elaborated project environment; direct mathlib and computable-analysis dependencies are shown as imported source nodes.")
    ])
  ]

private def dependencyNode (env : Environment) (projections : NameSet) (name : Name) (index : Nat) (module : String) (depth : Nat) : Json :=
  let (kind, rawRole, statement) := match env.find? name with
    | some ci => let (kind, role) := declarationKind ci; (kind, role, toString ci.type)
    | none => ("definition", "definition", s!"Lean declaration {name}")
  let role := if isStructure env name then "structure" else rawRole
  Json.mkObj [
    ("id", s!"const-{index}"),
    ("kind", "source"),
    ("declarationKind", kind),
    ("role", role),
    ("label", shortName name),
    ("statement", statement),
    ("namespace", name.toString),
    ("structuralProjection", Json.bool (projections.contains name)),
    ("locator", if module.startsWith "Mathlib." then s!"mathlib/{module}" else s!"computable-analysis/{module}"),
    ("citation", name.toString),
    ("dependencyDepth", toJson depth),
    ("dependencyBoundary", if depth >= maxDependencyDepth || isStructure env name then Json.bool true else Json.bool false),
    ("verification", Json.mkObj [
      ("state", "imported-checked"),
      ("scope", "imported"),
      ("closure", "closed")
    ])
  ]

private def dependencyEdges (env : Environment) (targets dependencies : Array Name) : Array Json :=
  let included := targets ++ dependencies
  let idFor (name : Name) : String × String :=
    if targets.contains name then
      let index := indexOf name targets
      match env.find? name with
      | some ci => (s!"decl-{index}", graphKind ci)
      | none => (s!"decl-{index}", "proposition")
    else
      (s!"const-{indexOf name dependencies}", "source")
  included.foldl (init := #[]) fun edges target =>
    match env.find? target with
    | some ci =>
      (bodyConstants ci).foldl (init := edges) fun edges dependency =>
        if included.contains dependency && dependency != target then
          let (targetId, targetKind) := idFor target
          let (sourceId, sourceKind) := idFor dependency
          edges.push <| Json.mkObj [
            ("id", s!"use-{sourceId}-{targetId}"),
            ("relation", "used-in-proof"),
            ("proof", if targetKind == "proposition" then targetId else ""),
            ("source", Json.mkObj [("id", sourceId), ("kind", sourceKind)]),
            ("target", Json.mkObj [("id", targetId), ("kind", targetKind)]),
            ("description", s!"{dependency} occurs in the elaborated Lean body of {target}.")
          ]
        else edges
    | none => edges

syntax "build_project_graph" : command

elab_rules : command
  | `(build_project_graph) => do
    let env ← getEnv
    let targets := projectNames env
    let depths := dependencyDepths env targets
    let dependencies := depths.map (·.1) |>.qsort Name.lt
    let projections := structuralProjectionNames env (targets ++ dependencies)
    let nodes := targets.mapIdx (fun i name =>
      match env.find? name with
      | some ci => projectNode env projections ci name i
      | none => Json.mkObj [("id", s!"decl-{i}"), ("kind", "proposition"),
          ("role", "theorem"), ("label", shortName name),
          ("statement", s!"Lean declaration {name}")]) ++
      dependencies.mapIdx (fun i name => dependencyNode env projections name i (moduleOf env name)
        (depths.find? (·.1 == name) |>.map (·.2) |>.getD 1))
    let edges := dependencyEdges env targets dependencies
    let report := Json.mkObj [
      ("schemaVersion", "1.0"),
      ("graphId", "math-net-project-declarations"),
      ("label", "math-net: Lean declaration dependencies"),
      ("nodes", toJson nodes),
      ("edges", toJson edges)
    ]
    liftIO <| IO.println report.compress
