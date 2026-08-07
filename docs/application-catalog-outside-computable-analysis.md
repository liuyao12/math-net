# Applications naturally outside computable-analysis

These are candidates for the next math-net layer.  They are theorem-sized
problems with concrete mathematical meaning, but their natural home is number
theory, discrete geometry, algebra, combinatorics, or classical analysis—not a
general computable-calculus library.

Basel is intentionally listed twice as one application with two proof records.
The Fourier proof and the Euler–Weierstrass proof should be compared as
different dependency landscapes.

| # | Application/problem | Candidate proof records |
|---:|---|---|
| 1 | **Basel problem, Fourier route:** `∑ n⁻² = π²/6` | Fourier series, Parseval, sine coefficients |
| 2 | **Basel problem, Euler–Weierstrass route** | Euler's sine product, logarithmic derivative, coefficient comparison |
| 3 | Count representations of `n` as two squares | prime factorization, Gaussian integers, Jacobi's formula |
| 4 | Prove the prime two-square criterion | elementary descent, Gaussian UFD, quadratic residues |
| 5 | Prove Fermat's square-area right-triangle theorem | infinite descent, Pythagorean parametrization, elliptic-curve obstruction |
| 6 | Solve `x² − D y² = 1` for a concrete `D` | continued fractions, Pell units, hyperbolic/geometric multiplication |
| 7 | Classify primitive Pythagorean triples | Euclid parametrization, rational unit circle, Gaussian factorization |
| 8 | Construct integer Heronian triangles | Heron's formula, Brahmagupta-style identities, lattice geometry |
| 9 | Determine when a quadratic form represents an integer | congruence obstructions, descent, genus/class-group methods |
| 10 | Prove a concrete case of quadratic reciprocity | Gauss lemma, lattice-point counting, cyclotomic roots of unity |
| 11 | Apply Wilson's theorem to factorial congruences | permutation involution, finite fields, polynomial roots |
| 12 | Solve a CRT system with a large modulus | constructive CRT, Bezout identities, finite ring decomposition |
| 13 | Find primitive roots modulo a specified prime | cyclic finite groups, factorization of `p−1`, discrete logarithms |
| 14 | Prove Lagrange's four-square theorem for a concrete family | quaternion norm identity, descent, theta-series route |
| 15 | Compute four-square representation counts | Jacobi theta identities, divisor sums, finite enumeration |
| 16 | Prove Pick's theorem for lattice polygons | triangulation, Euler characteristic, Ehrhart-style counting |
| 17 | Apply Minkowski's theorem to find a short lattice vector | convex-body geometry, determinant/area argument, reduction |
| 18 | Generate an Apollonian circle packing from one Descartes quadruple | Descartes quadratic form, matrix reflections, integral dynamics |
| 19 | Count necklaces or colorings up to symmetry | Burnside's lemma, cycle index, Polya enumeration |
| 20 | Relate graph colorings to the chromatic polynomial | deletion–contraction, finite recurrence, Tutte polynomial |

## Why these fit math-net

Each item has a concrete problem before the abstraction becomes visible. For
example:

- compute all solutions of a specific Pell equation;
- decide whether a specific quadratic form represents a target integer;
- count the square-sum or four-square representations of a factored integer;
- construct a lattice polygon with prescribed area and verify Pick's formula;
- generate the first several circles in an Apollonian packing;
- count colorings of a specified graph in two different ways.

The proof record can then expose whether the checked argument is elementary,
algebraic, geometric, Fourier-analytic, or dependent on a transcendental
black-box such as the sine product.  Computable-analysis can be cited where it
provides a useful representation or analytic bridge, but it need not own the
application.

## Suggested order

Start with Basel, Pell, quadratic reciprocity, Pick, and Burnside.  Together
they give math-net five distinct landscapes: Fourier analysis, Diophantine
approximation, finite arithmetic, lattice geometry, and finite group actions.
