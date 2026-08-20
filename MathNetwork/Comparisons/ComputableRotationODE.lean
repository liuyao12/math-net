import ComputableAnalysis.RotationPeanoBakerBridge

/-!
# Finite rotation: complex exponential and constant-coefficient ODE

The computable-analysis proof compares finite rational objects.  It does not
silently promote a Peano--Baker partial sum to a completed ODE solution.
-/

namespace MathNetwork.ComputableRotationODE

/-- A finite constant-coefficient Peano--Baker rotation partial sum is the
usual alternating cosine/sine matrix polynomial. -/
theorem rotationCenter_eq_constantPeanoBakerPartial
    (T : Rat) (n : Nat) :
    ComputableAnalysis.LinearODE.constantPeanoBakerSimplexPartial
        ComputableAnalysis.LinearODE.RotationSystem.generator T
        (ComputableAnalysis.RotationSeries.rotationTailTerms T n) =
      ComputableAnalysis.LinearODE.matrixAdd
        (ComputableAnalysis.LinearODE.matrixScale
          (ComputableAnalysis.RotationSeries.rotationCenter T n).re
          (ComputableAnalysis.LinearODE.matrixIdentity 2))
        (ComputableAnalysis.LinearODE.matrixScale
          (ComputableAnalysis.RotationSeries.rotationCenter T n).im
          ComputableAnalysis.LinearODE.RotationSystem.generator) :=
  ComputableAnalysis.RotationPeanoBakerBridge.rotationCenter_eq_constantPeanoBakerPartial T n

end MathNetwork.ComputableRotationODE
