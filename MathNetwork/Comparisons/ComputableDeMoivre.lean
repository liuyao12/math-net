import ComputableAnalysis.FiniteDeMoivreInterface

/-!
# Finite De Moivre on the rational circle

This is a geometric/algebraic benchmark with no angle parameter or completed
complex number. It says that taking a finite power commutes with multiplication
of rational points on the unit circle.
-/

namespace MathNetwork.ComputableDeMoivre

theorem pointPow_mul
    (p q : ComputableAnalysis.PiCirclePoint) (n : Nat) :
    ComputableAnalysis.RationalCircle.Trigonometry.pointPow
      (ComputableAnalysis.RationalCircle.Trigonometry.pointMul p q) n =
      ComputableAnalysis.RationalCircle.Trigonometry.pointMul
        (ComputableAnalysis.RationalCircle.Trigonometry.pointPow p n)
        (ComputableAnalysis.RationalCircle.Trigonometry.pointPow q n) :=
  ComputableAnalysis.RationalCircle.Trigonometry.pointPow_mul p q n

end MathNetwork.ComputableDeMoivre
