# List of 100 · verified calculus tranche

This tranche contains only declarations whose proof terms already exist in a
reputable Lean source. math-net adds wrappers or catalogue records; it does
not reproduce the proof bodies.

| # | common wrapper | checked source | status |
|---:|---|---|---|
| 14 | `MathNetwork.List100.basel` | mathlib `hasSum_zeta_two` | imported and kernel-checked |
| 15 | `MathNetwork.List100.fundamentalTheoremOfCalculus` | mathlib `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` | imported and kernel-checked |
| 17 | `MathNetwork.List100.deMoivre` | mathlib `Complex.cos_add_sin_mul_I_pow` | imported and kernel-checked |
| 26 | `MathNetwork.List100.leibnizPi` | mathlib `Real.tendsto_sum_pi_div_four` | imported and kernel-checked |
| 35 | `MathNetwork.List100.taylor` | mathlib `taylor_mean_remainder_lagrange_iteratedDeriv` | imported and kernel-checked |

The wrappers preserve the source theorem types as closely as possible. Their
purpose is to make the declarations visible to the graph extractor and give
the List-of-100 selector stable theorem nodes.

## External-route policy

The research pass found useful external material, but it is not yet treated as
a checked imported proof:

- `kewowski/EulerBasel` is a promising independent Basel route, but it has not
  been rebuilt under math-net’s Lean/mathlib pin;
- the external Riemann FTC development inspected for #15 contains `sorry`s;
- the historical Lean 3 Leibniz proof is a provenance record, not a current
  Lean 4 dependency;
- the historical Green’s theorem formalization was incorporated into mathlib.

These remain catalogue candidates until their proof terms are replayed or a
compatible checked import is available. No external route is presented as
kernel-verified merely because its source looks plausible.
