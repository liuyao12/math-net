import Mathlib.NumberTheory.ZetaValues

namespace MathNetwork.List100

theorem basel :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
  hasSum_zeta_two

end MathNetwork.List100
