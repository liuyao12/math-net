import Mathlib.Analysis.Real.Pi.Leibniz

namespace MathNetwork.List100

theorem leibnizPi :
    Filter.Tendsto
      (fun k : ℕ => ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1))
      Filter.atTop
      (nhds (Real.pi / 4)) :=
  Real.tendsto_sum_pi_div_four

end MathNetwork.List100
