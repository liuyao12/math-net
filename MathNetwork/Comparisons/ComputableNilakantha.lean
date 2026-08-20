import ComputableAnalysis.Nilakantha

/-!
# Nilakantha and Leibniz presentations of π

This adapter exposes the proved equivalence of two infinite rational-series
algorithms for π.  It is intentionally a small import-only bridge: the
termwise convergence proof remains in `computable-analysis`.
-/

namespace MathNetwork.ComputableNilakantha

/-- Nilakantha's accelerated alternating series and the Leibniz series
represent the same computable real number π. -/
theorem nilakantha_equiv_leibniz :
    ComputableAnalysis.piNilakantha.Equiv ComputableAnalysis.piLeibniz :=
  ComputableAnalysis.Nilakantha.equiv_piLeibniz

end MathNetwork.ComputableNilakantha
