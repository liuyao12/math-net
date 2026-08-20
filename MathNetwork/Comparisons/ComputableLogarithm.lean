import ComputableAnalysis.Logarithm

/-!
# Two certified constructions of `log 2`

The statement compares the alternating harmonic series with the literal
reciprocal integral on `[1, 2]`, both represented by rational interval
algorithms.
-/

namespace MathNetwork.ComputableLogarithm

/-- The alternating harmonic series and the reciprocal integral on `[1,2]`
represent the same computable real number, `log 2`. -/
theorem logTwoSeries_equiv_logTwoReciprocalIntegral :
    ComputableAnalysis.Logarithm.logTwoSeries.Equiv
      ComputableAnalysis.Logarithm.logTwoReciprocalIntegral :=
  ComputableAnalysis.Logarithm.logTwoSeries_equiv_logTwoReciprocalIntegral

end MathNetwork.ComputableLogarithm
