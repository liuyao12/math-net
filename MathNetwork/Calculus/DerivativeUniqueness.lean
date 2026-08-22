import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Uniqueness of the derivative: Mathlib and Tao Analysis

`teorth/analysis` states this as `Chapter10.derivative_unique` in
`Analysis/Section_10_1.lean`.  That particular source proof is complete, but
the upstream project pins an incompatible Mathlib revision.  The second route
below is therefore a source-preserving port: its body is checked here against
the current Mathlib, while its provenance remains explicit in the comparison
registry.
-/

namespace MathNetwork.Calculus

/-- The slope formulation used explicitly in Tao Analysis, Section 10.1. -/
theorem tao_hasDerivWithinAt_iff (X : Set ℝ) (x₀ : ℝ) (f : ℝ → ℝ) (L : ℝ) :
    HasDerivWithinAt f L X x₀ ↔
      (nhdsWithin x₀ (X \ {x₀})).Tendsto
        (fun x ↦ (f x - f x₀) / (x - x₀)) (nhds L) := by
  rw [hasDerivWithinAt_iff_tendsto_slope, slope_fun_def_field]

/-- A direct route through Mathlib's slope characterization. -/
theorem derivative_unique_mathlib_route {X : Set ℝ} {x₀ : ℝ}
    (hx₀ : ClusterPt x₀ (.principal (X \ {x₀}))) {f : ℝ → ℝ} {L L' : ℝ}
    (hL : HasDerivWithinAt f L X x₀) (hL' : HasDerivWithinAt f L' X x₀) :
    L = L' := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hL hL'
  rw [ClusterPt.eq_1] at hx₀
  letI : (nhdsWithin x₀ (X \ {x₀})).NeBot := hx₀
  exact tendsto_nhds_unique hL hL'

/-- The source-preserving Tao Analysis route.  It factors the same slope
characterization into the pedagogical formulation used in Section 10.1. -/
theorem derivative_unique_tao_route {X : Set ℝ} {x₀ : ℝ}
    (hx₀ : ClusterPt x₀ (.principal (X \ {x₀}))) {f : ℝ → ℝ} {L L' : ℝ}
    (hL : HasDerivWithinAt f L X x₀) (hL' : HasDerivWithinAt f L' X x₀) :
    L = L' := by
  rw [tao_hasDerivWithinAt_iff] at hL hL'
  rw [ClusterPt.eq_1] at hx₀
  letI : (nhdsWithin x₀ (X \ {x₀})).NeBot := hx₀
  exact tendsto_nhds_unique hL hL'

end MathNetwork.Calculus
