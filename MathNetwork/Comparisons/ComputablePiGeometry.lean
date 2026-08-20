import ComputableAnalysis.ArctanGeometry

/-!
# A geometric arctangent construction of π

This bridge stays below the larger `PiProofs` registry.  It compares two
direct, certified rational interval algorithms: circle area and four unit
sectors measured by geometric arctangent.
-/

namespace MathNetwork.ComputablePiGeometry

/-- Four unit geometric arctangent sectors and the circle-area algorithm
represent the same computable real number π. -/
theorem four_arctanGeom_one_equiv_piCircleArea :
    (((4 : Nat) * ComputableAnalysis.ArctanGeometry.arctanGeom (1 : Rat) :
      ComputableAnalysis.RealRaw).Equiv ComputableAnalysis.piCircleArea) :=
  ComputableAnalysis.ArctanGeometry.four_arctanGeom_one_equiv_piCircleArea

end MathNetwork.ComputablePiGeometry
