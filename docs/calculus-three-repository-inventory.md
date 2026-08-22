# Calculus: three-repository comparison inventory

This is the first calculus-focused intake for MathNet.  A theorem appears in
the interactive dependency graph only when its displayed route is genuinely
checked by the Lean kernel.  An external source can still be indexed, but it
must be visibly kept outside an exact merge until its version, theorem
statement, and proof status support one.

| Mathematical target | Mathlib route | ComputableAnalysis route | Tao Analysis route | Landscape state |
|---|---|---|---|---|
| Formal derivative of `x²` over the finite rational evaluator | Direct normalization in `MathNetwork.Calculus.quadratic_derivative_mathlib_route` | `ComputableAnalysis.Polynomial.eval_derivative_quadratic` | `HasDerivWithinAt.of_pow` is the analogous real derivative theorem | Exact two-route merge; Tao is an external `upstream-sorry` reference |
| Formal derivative of `x³` over the finite rational evaluator | Direct normalization in `MathNetwork.Calculus.cubic_derivative_mathlib_route` | `ComputableAnalysis.Polynomial.eval_derivative_cubic` | `HasDerivWithinAt.of_pow` specializes to the cubic | Exact two-route merge; Tao is an external `upstream-sorry` reference |
| Uniqueness of a within-derivative at an accumulation point | Direct slope-limit route | — | `Chapter10.derivative_unique` | Exact Mathlib/Tao comparison: Tao's complete source proof is source-preservingly ported and checked against the current Lake environment |
| Effective fundamental theorem of calculus | Completed-real calculus in Mathlib | Certified interval integration in ComputableAnalysis | `integ_eq_antideriv_sub` in Tao's Riemann-integral interface | Foundation-aligned between the two checked routes; Tao is an external `upstream-sorry` reference |
| Derivative rules for powers | Mathlib's real derivative API | Finite, executable polynomial derivative API | `Analysis/Section_10_1.lean` | A promising bridge family; only the two finite rational targets above are exact today |

## Why the first exact targets are finite polynomials

The common statement language is
`ComputableAnalysis.Polynomial.eval (Polynomial.derivative coefficients) x`
over `Rat`.  It avoids pretending that Mathlib's completed `ℝ`, Tao's real
analysis API, and `ComputableAnalysis.RealRaw` are definitionally the same
object.  The Mathlib route unfolds and normalizes the finite rational
calculation; the ComputableAnalysis route invokes its reusable derivative
theorem.  Lean checks that their resulting proposition types are literally
identical before the graph merges them.

That is a narrow but useful first comparison: the graph can show two real
proof-use branches without making a false claim about completeness or real
number representation.

`ComputableAnalysis.Rat` is Lean's lightweight kernel rational type from
`Init.Grind.Ordered.Rat`; it deliberately does not expose Mathlib's full
`CommRing` interface.  Consequently, an attractive-looking theorem such as
Mathlib's finite geometric-sum identity cannot simply be reused on a
ComputableAnalysis rational recurrence.  MathNet records such a pair as a
foundation/representation boundary until an explicit homomorphism bridge is
checked.  It does not manufacture a Mathlib-labelled proof edge by treating
the two rational APIs as interchangeable.

## Tao Analysis status

The reviewed source is [`teorth/analysis` at
`8f9e0fc`](https://github.com/teorth/analysis/tree/8f9e0fc5f063d0839f9b2bfc3ed9607b417877fb).
Its calculus theorem
[`HasDerivWithinAt.of_pow`](https://github.com/teorth/analysis/blob/8f9e0fc5f063d0839f9b2bfc3ed9607b417877fb/Analysis/Section_10_1.lean)
has an admitted body at that revision, and the project pins a different
Mathlib revision from this repository.  MathNet therefore records it as a
source-pinned, external comparison candidate in the inspector rather than
importing it, drawing invented dependency edges, or granting it a Lean
checkmark.  Once that route is sorry-free and a shared statement has been
proved, it can be promoted to an exact or foundation-aligned comparison.

`Chapter10.derivative_unique` is the exception currently used as a checked
Tao route: its source body is complete.  Because the project pins a different
Mathlib revision, MathNet carries a source-preserving port in
`MathNetwork.Calculus.DerivativeUniqueness`; Lean checks that port locally and
the explorer identifies it as a Tao Analysis route rather than pretending the
incompatible Lake dependency was imported directly.
