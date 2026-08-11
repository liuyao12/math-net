import Lean
import MathNetwork.Comparisons.Registry

open Lean Elab Command
open MathNetwork.Comparisons

private def routeJson {statement : Prop} (route : CheckedProof statement) : Json :=
  Json.mkObj [
    ("repository", route.repository),
    ("declaration", route.declaration)
  ]

private def comparisonJson (comparison : CheckedComparison) : Json :=
  Json.mkObj [
    ("id", comparison.id),
    ("routes", Json.arr (comparison.routes.map routeJson).toArray)
  ]

private def manifest : Json :=
  Json.mkObj [
    ("schemaVersion", "1.0"),
    ("comparisons", Json.arr (all.map comparisonJson).toArray)
  ]

elab "export_checked_comparisons" : command =>
  liftIO <| IO.println manifest.compress

export_checked_comparisons
