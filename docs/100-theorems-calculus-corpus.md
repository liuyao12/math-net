# Analysis-facing corpus from the 100 Theorems list

The `math-net` benchmark corpus should begin from Freek Wiedijk's
*Formalizing 100 Theorems* list, but it should not reproduce the list as a
scoreboard. The current Lean tracking page reports 84 of the 100 theorems
formalized in Lean. Our purpose is to attach alternative, locally checked
routes—even when mathlib already has a complete proof—and to compare the
interfaces those routes expose.

## First analysis-facing tranche

| List item | Target | Tracked Lean declaration | Calculus connection | Initial math-net route pair |
|---:|---|---|---|---|
| 4 | Pythagorean theorem | `EuclideanGeometry.dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two` | inner products, distance, angle, and `π` | coordinate geometry / rotation-trigonometry |
| 9 | Area of a circle | `Theorems100.area_disc`* | measure integral versus geometric/Riemann area | general measure integral / Riemann partitions |
| 14 | Basel problem | `hasSum_zeta_two` | infinite series, Fourier analysis, or Euler products | Fourier / Euler–Weierstrass |
| 15 | Fundamental theorem of integral calculus | `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` | the central completeness/integration boundary | general interval integral / Riemann integral |
| 17 | De Moivre’s formula | `Complex.cos_add_sin_mul_I_pow` | complex exponential, trigonometry, and rotations | complex exponential / geometric rotation |
| 26 | Leibniz series for `π` | `Real.tendsto_sum_pi_div_four` | alternating series and inverse tangent | arctangent integral / power series |
| 27 | Sum of the angles of a triangle | `EuclideanGeometry.angle_add_angle_add_angle_eq_pi` | Euclidean geometry and the meaning of `π` | synthetic geometry / coordinates and trig |
| 34 | Divergence of the harmonic series | `Real.tendsto_sum_range_one_div_nat_succ_atTop` | limits, comparison, and integral estimates | condensation/comparison / integral estimate |
| 35 | Taylor’s theorem | `taylor_mean_remainder_lagrange` | derivatives, remainder estimates, and completeness | mean-value route / explicit remainder integral |
| 38 | Arithmetic–geometric mean inequality | `Real.geom_mean_le_arith_mean_weighted` | convexity and a calculus proof alongside the algebraic proof | weighted AM–GM / logarithmic convexity |
| 40 | Minkowski’s fundamental theorem | `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure` | volume, convexity, and lattice geometry | measure-theoretic / elementary planar geometry |
| 75 | Mean value theorem | `exists_deriv_eq_slope` | derivatives and the intermediate-value mechanism | standard derivative proof / explicit interval proof |
| 76 | Fourier series | `hasSum_fourier_series_L2` | integration, orthogonality, and completeness | complex basis / sine–cosine basis |
| 79 | Intermediate value theorem | `intermediate_value_Icc` | completeness of the real line and continuous functions | supremum proof / nested interval or computable certificate |

The first implementation targets should be items 9, 14, 15, 17, 26, 35,
75, 76, and 79. They cover integration, series, complex analysis,
Fourier analysis, differentiation, and the completeness boundary while still
having concrete application statements.

\* The online tracking page gives `Theorems100.area_disc`, but that exact
declaration is not currently present in this local mathlib checkout. It is
therefore a cross-repository import target until we locate or re-establish the
source. Every catalog entry will undergo this local declaration check before
it becomes a graph node.

## Route policy

For each target, math-net records at least two route records when meaningful:

1. the existing mathlib route, treated as the library-complete baseline;
2. a selected route with a narrower interface or a different mathematical
   presentation.

The second route is not required to be shorter. It is valuable if it makes a
dependency visible: for example, a Riemann proof may expose interval
partitions and uniform continuity while avoiding the full measure-integral
interface. The record must say whether it is kernel-checked, which imported
lemmas are black boxes, and whether the route is fully closed or conditional.

“Analysis-facing” does not mean that calculus is logically necessary. A
theorem belongs here if it has a meaningful route through analysis, broadly
understood. This includes trigonometric geometry, complex exponentials,
Fourier methods, probability, limits, numerical approximation, or analytic
number theory. A theorem may therefore qualify even when its standard proof is
algebraic and calculus is only an illuminating alternative.

We use three inclusion labels:

- **essential:** the target naturally requires limits, derivatives, integrals,
  infinite series, or completeness in the selected route;
- **perspective:** an analytic route is optional but mathematically revealing,
  as with a trigonometric proof of a geometric or number-theoretic identity;
- **computational:** analysis supplies certified approximation, effective
  bounds, or a numerical application rather than the core theorem.

## Relationship to the project graph

The list item is a proposition/application node. Its competing proofs remain
attached records, not permanent proof nodes. Selecting a route displays only
the declarations used in that route, through the graph's single
`used-in-proof` relation. The list number, library declaration, and route
classification are metadata and do not create dependency arrows.
