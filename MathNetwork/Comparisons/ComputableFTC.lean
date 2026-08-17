import ComputableAnalysis.FTC

/-!
# Computable effective fundamental theorem of calculus

This is a deliberately thin adapter.  The proof itself lives in
`computable-analysis`; math-net gives the checked declaration a stable place
in the landscape beside Mathlib's interval-integral FTC.
-/

namespace MathNetwork.ComputableFTC

/-- A certified Riemann algorithm for a derivative and the corresponding
endpoint-difference algorithm represent the same computable real. -/
theorem effectiveFTC_equiv_endpoint
    {F dF : ComputableAnalysis.RealFunRaw} {a b : Rat}
    (h : ComputableAnalysis.EffectiveFTC F dF a b) :
    (ComputableAnalysis.FTC.riemannRawOfEffectiveFTC h).Equiv
      (ComputableAnalysis.FTC.endpointRawOfEffectiveFTC h) :=
  ComputableAnalysis.FTC.effectiveFTC_equiv_endpoint h

end MathNetwork.ComputableFTC
