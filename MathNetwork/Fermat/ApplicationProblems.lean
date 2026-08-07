import MathNetwork.Fermat.Benchmarks
import MathNetwork.Fermat.Geometry
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

namespace MathNetwork.Fermat

/-!
# Application problems around sums of two squares

This file is deliberately a catalogue, not a second proof of every theorem in
the subject.  The checked entries are small but theorem-shaped interfaces that
can be used as regression tests for different foundations.  The planned
entries are propositions: they make an honest target visible without inserting
`sorry`, `admit`, or an axiom into the development.

The arctangent entry cites Mathlib's real arctangent addition theorem through
`arctan_compose_13_17`; the deeper geometric/computable-analysis boundary is
recorded in the catalogue metadata below.
-/

def squareSum (a b : ℤ) : ℤ := a * a + b * b

def isSquareSum (n : ℕ) : Prop := ∃ a b : ℕ, a ^ 2 + b ^ 2 = n

theorem squareSum_comm (a b : ℤ) : squareSum a b = squareSum b a := by
  simp [squareSum, add_comm]

theorem squareSum_neg_left (a b : ℤ) : squareSum (-a) b = squareSum a b := by
  simp [squareSum]

theorem squareSum_neg_right (a b : ℤ) : squareSum a (-b) = squareSum a b := by
  simp [squareSum]

theorem squareSum_29 : squareSum 5 2 = 29 := by
  norm_num [squareSum]

theorem squareSum_65_two_representations :
    squareSum 1 8 = 65 ∧ squareSum 4 7 = 65 := by
  norm_num [squareSum]

theorem squareSum_composition (a b c d : ℤ) :
    squareSum (a * c - b * d) (a * d + b * c) =
      squareSum a b * squareSum c d := by
  simp [squareSum]
  ring

theorem squareSum_composition_13_17 :
    squareSum (3 * 4 - 2 * 1) (3 * 1 + 2 * 4) = 13 * 17 := by
  norm_num [squareSum]

theorem rationalCirclePoint_on_unit_circle {a b : ℚ}
    (h : a * a + b * b ≠ 0) :
    (rationalCirclePoint a b).1 ^ 2 +
      (rationalCirclePoint a b).2 ^ 2 = 1 := by
  dsimp [rationalCirclePoint]
  have hpow : a ^ 2 + b ^ 2 ≠ 0 := by
    intro hz
    apply h
    nlinarith [sq_nonneg a, sq_nonneg b]
  field_simp [hpow]
  ring_nf

theorem rationalCirclePoint_5_2_certified :
    (rationalCirclePoint 5 2).1 ^ 2 +
      (rationalCirclePoint 5 2).2 ^ 2 = 1 := by
  rw [rationalCirclePoint_5_2]
  norm_num

def signedCoordinate (n i : ℕ) : ℤ := (i : ℤ) - n

def signedRepresentationCount (n : ℕ) : ℕ :=
  ((Finset.product
      (Finset.range (2 * n + 1))
      (Finset.range (2 * n + 1))).filter
    (fun p => squareSum (signedCoordinate n p.1) (signedCoordinate n p.2) = n)).card

theorem signedRepresentationCount_13 : signedRepresentationCount 13 = 8 := by
  native_decide

theorem signedRepresentationCount_65 : signedRepresentationCount 65 = 16 := by
  native_decide

theorem signedRepresentationCount_29 : signedRepresentationCount 29 = 8 := by
  native_decide

theorem arctan_application_13_17 :
    Real.arctan (2 / 3 : ℝ) + Real.arctan (1 / 4 : ℝ) =
      Real.arctan (11 / 10 : ℝ) := by
  exact arctan_compose_13_17

theorem tangent_application_13_17 :
    MathNetwork.Machin.tangentCompose (2 / 3 : ℚ) (1 / 4 : ℚ) = 11 / 10 := by
  exact tangent_compose_13_17

theorem pythagorean_parametrization (m n : ℤ) :
    squareSum (m * m - n * n) (2 * m * n) =
      squareSum m n * squareSum m n := by
  simp [squareSum]
  ring

theorem area_of_3_4_5_triangle :
    (3 : ℚ) * 4 / 2 = 6 := by
  norm_num

theorem area_of_3_4_5_is_not_a_square :
    ¬ ∃ k : ℕ, (k : ℚ) ^ 2 = 6 := by
  rintro ⟨k, hk⟩
  have hk' : (k : ℚ) ^ 2 = (6 : ℚ) := hk
  have hk_le : k ≤ 2 := by
    by_contra hnot
    have hk3 : (3 : ℚ) ≤ k := by exact_mod_cast (show 3 ≤ k by omega)
    nlinarith
  interval_cases k <;> norm_num at hk'

theorem mod_four_obstruction_3 : ¬ isSquareSum 3 := by
  exact not_sumSquares_3

theorem mod_four_obstruction_7 : ¬ isSquareSum 7 := by
  exact not_sumSquares_7

/-! The following are explicit targets for future proof routes. -/

def primeFactorCriterion : Prop :=
  ∀ n : ℕ, isSquareSum n ↔
    ∀ p : ℕ, Nat.Prime p → p % 4 = 3 → Even (n.factorization p)

def sumOfTwoSquaresCountFormula : Prop :=
  ∀ n : ℕ, signedRepresentationCount n =
    4 * (n.factorization.support.filter fun p => p % 4 = 1).prod
      (fun p => n.factorization p + 1)

def prime_one_mod_four_representation : Prop :=
  ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 → isSquareSum p

def fermat_right_triangle_obstruction : Prop :=
  ¬ ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧
    a ^ 2 + b ^ 2 = c ^ 2 ∧
    ∃ k : ℕ, (a * b / 2) = k ^ 2

def primitive_representation_uniqueness : Prop :=
  ∀ {p a b c d : ℕ}, Nat.Prime p → p % 4 = 1 →
    a ^ 2 + b ^ 2 = p → c ^ 2 + d ^ 2 = p →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

def gaussian_euclidean_route : Prop :=
  ∀ {n : ℕ}, isSquareSum n →
    ∃ z : GaussianPair, z.normSq = n

def arctan_geometry_bridge : Prop :=
  ∀ {a b : ℚ}, 0 < a → 0 ≤ b →
    ∃ θ : ℝ, Real.tan θ = (b / a : ℝ) ∧
      ((a : ℝ) ^ 2 + (b : ℝ) ^ 2) ≠ 0

def machins_formula_application : Prop :=
  4 * Real.arctan (1 / 5 : ℝ) - Real.arctan (1 / 239 : ℝ) = Real.pi / 4

def rational_circle_to_integer_representation : Prop :=
  ∀ {n : ℕ} {x y : ℚ}, x ^ 2 + y ^ 2 = 1 →
    ∃ a b : ℤ, x = a / n ∧ y = b / n ∧ a * a + b * b = n * n

structure ApplicationEntry where
  id : String
  statement : String
  status : String
  declaration : String
  imports : List String
deriving Repr

def applicationCatalogue : List ApplicationEntry :=
  [ { id := "composition-law"
      statement := "The two-square identity composes representations."
      status := "kernel-checked"
      declaration := "squareSum_composition"
      imports := ["Mathlib.Tactic"] }
    , { id := "prime-factor-criterion"
        statement := "A factored n is a sum of two squares exactly when 3 mod 4 primes have even exponent."
        status := "planned"
        declaration := "primeFactorCriterion"
        imports := ["Mathlib.Data.Nat.Factorization"] }
    , { id := "representation-count"
        statement := "Compute signed r₂(n) and compare it with the factorization formula."
        status := "partially checked"
        declaration := "signedRepresentationCount_13, signedRepresentationCount_29, signedRepresentationCount_65"
        imports := ["Mathlib.Data.Finset.Interval"] }
    , { id := "prime-1-mod-4"
        statement := "Every prime congruent to 1 modulo 4 has a two-square representation."
        status := "planned"
        declaration := "prime_one_mod_four_representation"
        imports := ["Mathlib.Data.Nat.Prime.Basic"] }
    , { id := "right-triangle-area"
        statement := "A primitive integer right triangle cannot have square area."
        status := "planned"
        declaration := "fermat_right_triangle_obstruction"
        imports := ["Mathlib.Tactic"] }
    , { id := "rational-circle"
        statement := "Pythagorean parametrization produces rational points on the unit circle."
        status := "kernel-checked"
        declaration := "rationalCirclePoint_on_unit_circle"
        imports := ["Mathlib.Tactic"] }
    , { id := "arctan-composition"
        statement := "The rational slopes 2/3 and 1/4 compose to 11/10."
        status := "kernel-checked; imported Mathlib theorem"
        declaration := "arctan_application_13_17"
        imports := ["Real.arctan_add", "Real.tan_arctan"] }
    , { id := "computable-arctan-geometry"
        statement := "A geometric arctangent construction supplies the angle/slope bridge."
        status := "planned cross-project import"
        declaration := "RationalCircle.GeometricTrig.FirstQuadrantArctanWitness"
        imports := ["ComputableAnalysis.ArctanGeometry"] }
    , { id := "gaussian-route"
        statement := "The sum-of-two-squares problem can be transported to Gaussian pairs."
        status := "planned"
        declaration := "gaussian_euclidean_route"
        imports := ["MathNetwork.Fermat.Basic"] }
    , { id := "uniqueness"
        statement := "Prime representations are unique up to signs and order."
        status := "planned"
        declaration := "primitive_representation_uniqueness"
        imports := ["Mathlib.Data.Nat.Prime.Basic"] }
    , { id := "count-formula"
        statement := "The signed representation count is determined by 1 mod 4 prime exponents."
        status := "planned"
        declaration := "sumOfTwoSquaresCountFormula"
        imports := ["Mathlib.Data.Nat.Factorization"] }
    , { id := "machin"
        statement := "Machin's formula gives a transcendental-function application."
        status := "planned cross-project comparison"
        declaration := "machins_formula_application"
        imports := ["ComputableAnalysis.ArctanGeometry"] } ]

end MathNetwork.Fermat
