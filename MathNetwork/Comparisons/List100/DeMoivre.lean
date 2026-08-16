import Mathlib.Analysis.Complex.Trigonometric

namespace MathNetwork.List100

theorem deMoivre (n : ℕ) (z : ℂ) :
    (Complex.cos z + Complex.sin z * Complex.I) ^ n =
      Complex.cos (↑n * z) + Complex.sin (↑n * z) * Complex.I :=
  Complex.cos_add_sin_mul_I_pow n z

end MathNetwork.List100
