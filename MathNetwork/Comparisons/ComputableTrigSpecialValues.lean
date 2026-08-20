import ComputableAnalysis.TrigSpecialValues

/-!
# A certified 45-degree unit-circle identity

This adapter preserves the computable-analysis statement over `RealRaw`.  It
is a geometric-trigonometric application awaiting a representation bridge to
become an exact comparison with Mathlib's completed-real identity.
-/

namespace MathNetwork.ComputableTrigSpecialValues

/-- The certified 45-degree sine and cosine values satisfy the unit-circle
identity over computable raw reals. -/
theorem cosFortyFive_square_add_sinFortyFive_square_equiv_one :
    (ComputableAnalysis.RationalCircle.GeometricTrig.SpecialAngles.rawSquare
      ComputableAnalysis.RationalCircle.GeometricTrig.SpecialAngles.cosFortyFiveValue +
      ComputableAnalysis.RationalCircle.GeometricTrig.SpecialAngles.rawSquare
        ComputableAnalysis.RationalCircle.GeometricTrig.SpecialAngles.sinFortyFiveValue).Equiv
      (ComputableAnalysis.RealRaw.ofRat (1 : Rat)) :=
  ComputableAnalysis.RationalCircle.GeometricTrig.SpecialAngles.cosFortyFive_square_add_sinFortyFive_square_equiv_one

end MathNetwork.ComputableTrigSpecialValues
