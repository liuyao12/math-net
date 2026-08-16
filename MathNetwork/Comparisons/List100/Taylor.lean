import Mathlib.Analysis.Calculus.Taylor

namespace MathNetwork.List100

theorem taylor
    {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ (n + 1) f (Set.uIcc x₀ x)) :
    ∃ x' ∈ Set.uIoo x₀ x,
      f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
        iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / Nat.factorial (n + 1) :=
  taylor_mean_remainder_lagrange_iteratedDeriv hx hf

end MathNetwork.List100
