import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace MathNetwork.Fermat

/-!
# The geometric/lattice benchmark

An integer pair is a lattice point in the plane.  Its squared distance from
the origin is the sum-of-two-squares expression, while the arctangent of its
slope records its direction.  This file formalizes the concrete 29 benchmark
without hiding the arithmetic inside complex exponentials.
-/

structure LatticePoint where
  x : ℤ
  y : ℤ

def LatticePoint.normSq (v : LatticePoint) : ℤ := v.x * v.x + v.y * v.y

def LatticePoint.slope (v : LatticePoint) : ℚ := (v.y : ℚ) / v.x

noncomputable def LatticePoint.angle (v : LatticePoint) : ℝ :=
  Real.arctan (v.slope : ℝ)

theorem lattice_angle_tan (v : LatticePoint) :
    Real.tan v.angle = (v.slope : ℝ) := by
  simp [LatticePoint.angle, Real.tan_arctan]

theorem lattice_point_29_norm :
    (LatticePoint.mk 5 2).normSq = 29 := by
  norm_num [LatticePoint.normSq]

theorem lattice_point_29_slope :
    (LatticePoint.mk 5 2).slope = (2 / 5 : ℚ) := by
  norm_num [LatticePoint.slope]

theorem lattice_point_29_angle_tan :
    Real.tan (LatticePoint.mk 5 2).angle = (2 / 5 : ℝ) := by
  rw [lattice_angle_tan, lattice_point_29_slope]
  norm_num

def geometricWitness29 : Prop :=
  ∃ v : LatticePoint, v.normSq = 29 ∧ Real.tan v.angle = (2 / 5 : ℝ)

theorem geometricWitness29_proof : geometricWitness29 := by
  refine ⟨LatticePoint.mk 5 2, lattice_point_29_norm, ?_⟩
  exact lattice_point_29_angle_tan

end MathNetwork.Fermat
