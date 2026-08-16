import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

namespace MathNetwork.Fermat

/-- A Gaussian integer written as a pair, so the benchmark statement does not
mention the symbol `i`. -/
structure GaussianPair where
  re : Int
  im : Int
deriving DecidableEq, Repr

/-- The pair multiplication suggested by planar rotation composition. -/
def GaussianPair.mul (z w : GaussianPair) : GaussianPair :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- Squared Euclidean length, also the Gaussian norm. -/
def GaussianPair.normSq (z : GaussianPair) : Int :=
  z.re * z.re + z.im * z.im

@[simp] theorem normSq_mul (z w : GaussianPair) :
    (z.mul w).normSq = z.normSq * w.normSq := by
  simp [GaussianPair.mul, GaussianPair.normSq]
  ring

theorem euclid_lemma {p a b : Nat} (hp : Nat.Prime p)
    (h : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  exact hp.dvd_mul.mp h

end MathNetwork.Fermat
