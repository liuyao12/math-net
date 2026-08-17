import ComputableAnalysis.FiniteFourierCertificate

/-!
# A finite Fourier/Parseval comparison target

The theorem is a reusable exact four-point Fourier identity over rational
coordinates.  It is intentionally finite: it does not claim an infinite
Fourier convergence theorem or invoke completeness.
-/

namespace MathNetwork.ComputableFourier

theorem fourPointFourierTransform_parseval (x₀ x₁ x₂ x₃ : Rat) :
    ComputableAnalysis.QComplex.normSq
        (ComputableAnalysis.fourPointFourierTransform x₀ x₁ x₂ x₃ 0) +
        ComputableAnalysis.QComplex.normSq
          (ComputableAnalysis.fourPointFourierTransform x₀ x₁ x₂ x₃ 1) +
        ComputableAnalysis.QComplex.normSq
          (ComputableAnalysis.fourPointFourierTransform x₀ x₁ x₂ x₃ 2) +
        ComputableAnalysis.QComplex.normSq
          (ComputableAnalysis.fourPointFourierTransform x₀ x₁ x₂ x₃ 3) =
      4 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2) :=
  ComputableAnalysis.fourPointFourierTransform_parseval x₀ x₁ x₂ x₃

end MathNetwork.ComputableFourier
