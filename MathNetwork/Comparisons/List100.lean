import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact List-of-100 comparison wrappers

These declarations intentionally contain no new proof bodies. They expose
already checked mathlib theorems under math-net names so the dependency graph
can index their exact elaborated statements. Alternative proof repositories
will later contribute matching declarations or catalogue records.
-/

namespace MathNetwork.List100

theorem basel :
    HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
  hasSum_zeta_two

theorem deMoivre (n : ℕ) (z : ℂ) :
    (Complex.cos z + Complex.sin z * Complex.I) ^ n =
      Complex.cos (↑n * z) + Complex.sin (↑n * z) * Complex.I :=
  Complex.cos_add_sin_mul_I_pow n z

theorem leibnizPi :
    Filter.Tendsto
      (fun k : ℕ => ∑ i ∈ Finset.range k, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1))
      Filter.atTop
      (nhds (Real.pi / 4)) :=
  Real.tendsto_sum_pi_div_four

theorem taylor
    {f : ℝ → ℝ} {x x₀ : ℝ} {n : ℕ}
    (hx : x₀ ≠ x)
    (hf : ContDiffOn ℝ (n + 1) f (Set.uIcc x₀ x)) :
    ∃ x' ∈ Set.uIoo x₀ x,
      f x - taylorWithinEval f n (Set.uIcc x₀ x) x₀ x =
        iteratedDeriv (n + 1) f x' * (x - x₀) ^ (n + 1) / Nat.factorial (n + 1) :=
  taylor_mean_remainder_lagrange_iteratedDeriv hx hf

theorem fundamentalTheoremOfCalculus
    {a b : ℝ} {f f' : ℝ → ℝ}
    (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' MeasureTheory.volume a b) :
    (∫ y in a..b, f' y) = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint

end MathNetwork.List100
