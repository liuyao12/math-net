import Lean
import MathNetwork.Comparisons.Registry

open Lean Elab Command
open MathNetwork.Comparisons

private def routeJson {statement : Prop} (route : CheckedProof statement) : Json :=
  Json.mkObj [
    ("repository", route.repository),
    ("declaration", route.declaration),
    ("title", route.title),
    ("description", route.description)
  ]

private def comparisonJson (comparison : CheckedComparison) : Json :=
  Json.mkObj [
    ("id", comparison.id),
    ("title", comparison.title),
    ("description", comparison.description),
    ("routes", Json.arr (comparison.routes.map routeJson).toArray)
  ]

private def alignedComparisonJson (comparison : FoundationAlignedComparison) : Json :=
  Json.mkObj [
    ("id", comparison.id),
    ("title", comparison.title),
    ("description", comparison.description),
    ("alignment", "foundation-aligned"),
    ("note", comparison.note),
    ("mathematicalCore", comparison.mathematicalCore),
    ("routes", Json.arr (comparison.routes.map (fun (repository, declaration, foundation) =>
      Json.mkObj [
        ("repository", repository),
        ("declaration", declaration),
        ("foundation", foundation)
      ]
    )).toArray)
  ]

private def presentationJson (presentation : CheckedComparison) : Json :=
  Json.mkObj [
    ("id", presentation.id),
    ("title", presentation.title),
    ("description", presentation.description),
    ("alignment", "presentation"),
    ("routes", Json.arr (presentation.routes.map routeJson).toArray)
  ]

private def manifest : Json :=
  Json.mkObj [
    ("schemaVersion", "1.0"),
    ("comparisons", Json.arr ((all.map comparisonJson ++
      aligned.map alignedComparisonJson ++ presentations.map presentationJson).toArray))
  ]

elab "export_checked_comparisons" : command =>
  liftIO <| IO.println manifest.compress

export_checked_comparisons
