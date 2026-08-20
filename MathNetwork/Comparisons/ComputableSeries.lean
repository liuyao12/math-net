import ComputableAnalysis.Series

/-!
# A certified telescoping-series application

This adapter exposes a finished computable-analysis result without recasting
it in Mathlib's real numbers. The theorem is a useful low-level benchmark:
the rational partial sums of the reciprocal triangular series converge, as a
certified `RealRaw`, to `2`.
-/

namespace MathNetwork.ComputableSeries

/-- The computable rational interval algorithm for
`Σ n, 2 / ((n + 1) * (n + 2))` represents the exact value `2`. -/
theorem triangularTelescopingRaw_equiv_two :
    ComputableAnalysis.Series.triangularTelescopingRaw.Equiv
      (ComputableAnalysis.RealRaw.ofRat 2) :=
  ComputableAnalysis.Series.triangularTelescopingRaw_equiv_two

/-- The alternating-series interval used for the computable sine evaluator is
exactly its Taylor partial-sum interval on the controlled input range. -/
theorem sineAlternatingRaw_interval_eq_sineTaylorInterval
    {x : Rat} (hx : 0 <= x) (hterms : ComputableAnalysis.qabs x <= 2) (n : Nat) :
    (ComputableAnalysis.Series.AlternatingRaw.sineAlternatingRaw x hterms).interval n =
      ComputableAnalysis.Series.evenOddInterval
        (ComputableAnalysis.FormalPowerSeries.sineTaylorPartial x) n :=
  ComputableAnalysis.Series.AlternatingRaw.sineAlternatingRaw_interval_eq_sineTaylorInterval hx hterms n

end MathNetwork.ComputableSeries
