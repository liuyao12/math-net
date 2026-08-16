import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace MathNetwork.List100

theorem fundamentalTheoremOfCalculus
    {a b : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' MeasureTheory.volume a b) :
    (∫ y in a..b, f' y) = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint

end MathNetwork.List100
