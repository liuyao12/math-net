import MathNetwork.Fermat.Basic
import MathNetwork.Machin.Basic

namespace MathNetwork.Fermat

/-!
# Low-level benchmark problems

These are deliberately small targets.  They give a reader something concrete
to calculate before selecting a proof of the general theorem, and they give
the dependency network stable regression points.
-/

def isSumOfTwoSquares (n : Nat) : Prop :=
  ∃ a b : Nat, a ^ 2 + b ^ 2 = n

theorem sumSquares_13 : isSumOfTwoSquares 13 := by
  exact ⟨3, 2, by norm_num [isSumOfTwoSquares]⟩

theorem sumSquares_17 : isSumOfTwoSquares 17 := by
  exact ⟨4, 1, by norm_num [isSumOfTwoSquares]⟩

theorem sumSquares_29 : isSumOfTwoSquares 29 := by
  exact ⟨5, 2, by norm_num [isSumOfTwoSquares]⟩

theorem sumSquares_65 : isSumOfTwoSquares 65 := by
  exact ⟨8, 1, by norm_num [isSumOfTwoSquares]⟩

theorem two_representations_65 :
    (1 : Nat) ^ 2 + 8 ^ 2 = 65 ∧ 4 ^ 2 + 7 ^ 2 = 65 := by
  norm_num

theorem compose_13_17 :
    GaussianPair.mul ⟨3, 2⟩ ⟨4, 1⟩ = ⟨10, 11⟩ := by
  rfl

theorem sumSquares_221_by_composition : isSumOfTwoSquares 221 := by
  exact ⟨10, 11, by norm_num [isSumOfTwoSquares]⟩

theorem norm_composition_13_17 :
    (13 : Int) * 17 = 221 := by
  norm_num

def rationalCirclePoint (a b : ℚ) : ℚ × ℚ :=
  ((a * a - b * b) / (a * a + b * b),
    (2 * a * b) / (a * a + b * b))

theorem rationalCirclePoint_5_2 :
    rationalCirclePoint 5 2 = ((21 / 29 : ℚ), (20 / 29 : ℚ)) := by
  norm_num [rationalCirclePoint]

theorem rationalCirclePoint_5_2_on_unit_circle :
    (21 / 29 : ℚ) ^ 2 + (20 / 29 : ℚ) ^ 2 = 1 := by
  norm_num

theorem arctan_compose_13_17 :
    Real.arctan (2 / 3 : ℝ) + Real.arctan (1 / 4 : ℝ) =
      Real.arctan (11 / 10 : ℝ) := by
  rw [Real.arctan_add]
  · norm_num
  · norm_num

theorem tangent_compose_13_17 :
    MathNetwork.Machin.tangentCompose (2 / 3 : ℚ) (1 / 4 : ℚ) = 11 / 10 := by
  norm_num [MathNetwork.Machin.tangentCompose]

theorem not_sumSquares_3 : ¬ isSumOfTwoSquares 3 := by
  rintro ⟨a, b, h⟩
  have ha : a ≤ 1 := by nlinarith [Nat.zero_le b]
  have hb : b ≤ 1 := by nlinarith [Nat.zero_le a]
  interval_cases a <;> interval_cases b <;> norm_num at h

theorem not_sumSquares_7 : ¬ isSumOfTwoSquares 7 := by
  rintro ⟨a, b, h⟩
  have ha : a ≤ 2 := by nlinarith [Nat.zero_le b]
  have hb : b ≤ 2 := by nlinarith [Nat.zero_le a]
  interval_cases a <;> interval_cases b <;> norm_num at h

theorem pythagorean_3_4_5 : 3 ^ 2 + 4 ^ 2 = 5 ^ 2 := by
  norm_num

theorem sumSquares_mul_benchmark
    (z w : GaussianPair) :
    (z.mul w).normSq = z.normSq * w.normSq := by
  exact normSq_mul z w

end MathNetwork.Fermat
