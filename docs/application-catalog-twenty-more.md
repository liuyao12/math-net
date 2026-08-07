# Twenty applications beyond Fermat

Fermat's sum-of-two-squares theorem is the first benchmark.  The following
twenty applications are similar in spirit: each starts with a concrete
mathematical problem, admits an elementary or geometric formulation, and may
lead to a substantially different proof through calculus or computable
analysis.

The status column indicates whether computable-analysis already appears to
contain reusable infrastructure, not whether math-net has completed the
application.

| # | Application/problem | Concrete benchmark | Candidate routes | Existing CA interface |
|---:|---|---|---|---|
| 1 | Machin's formula for π | `π/4 = 4 arctan(1/5) − arctan(1/239)` | rational tangent algebra; geometric arctan; series | arctangent presentations and Machin rows |
| 2 | Leibniz's formula for π | `π/4 = 1 − 1/3 + 1/5 − ⋯` | alternating series; geometric arctan integral | `ArctanPresentations`, series modules |
| 3 | Archimedean circle bounds | construct rational lower/upper bounds for π with explicit error | polygon geometry; finite refinement | `RationalCircle` |
| 4 | Area–circumference equality for the circle | prove the two finite π constructions agree | polygonal geometry; finite bridges | `PiProofs`, `RationalCircle` |
| 5 | Basel problem | `∑ 1/n² = π²/6` | Fourier/Parseval; products; integral transforms | `Basel`, geometric π bridges |
| 6 | Reciprocal quartic integral | `∫₋¹¹ (1+x²)/(x⁴−x²+1) dx = π` | algebraic partial fractions; arctangent | `ReciprocalQuarticPi` |
| 7 | Cauchy integral for π | `∫_{−∞}^{∞} 1/(1+x²) dx = π` | compactification; finite interval certificates | `CauchyPi` |
| 8 | Logarithmic π identity | `π = 4 arctan(1) +` a logarithmic correction | integration by parts; `log`/arctan bridge | `LogarithmicPi` |
| 9 | Coordinate substitution in an integral | transport `∫ 2x/(1+x²) dx` to `∫ 1/(1+t) dt` | finite partitions; substitution | `IntegralIdentities` |
| 10 | Derivative of `x arctan x` | `d(x arctan x)=arctan x+x/(1+x²)` on `[0,1]` | finite difference certificates; FTC | `IntegralIdentities` |
| 11 | Derivative of arctangent | `d(arctan x)=1/(1+x²)` on a certified interval | geometric rectangle construction; difference quotients | `ArctanGeometry` |
| 12 | Exponential initial-value problem | construct `eˣ` from finite approximants with `f'=f`, `f(0)=1` | power series; common-prefix certificates | `Exp`, `ExpProofs` |
| 13 | Rotation initial-value problem | `C' = −S`, `S' = C`, with `(C(0),S(0))=(1,0)` | finite matrices; power series; ODE uniqueness | `RotationInitialValues`, `RotationSeries` |
| 14 | Pythagorean identity from rotation | `cos² t + sin² t = 1` for computable rotation approximants | rational circle; ODE invariant; exp bridge | `GeometricPiRotation`, `RotationCalculus` |
| 15 | Euler's identity as a dependency benchmark | `exp(iπ) + 1 = 0` | rotation route; complex exp/log route | `PiComplex`, `Exp`, `Rotation*` |
| 16 | Finite Peano–Baker solution | certify a sampled linear system by an explicit finite word expansion | rational matrices; noncommutative products | `PeanoBaker` |
| 17 | Variation of constants | verify a concrete inhomogeneous linear ODE solution | finite transition matrices; integral certificates | `PeanoBaker`, `Differential` |
| 18 | Algebraic square-root function | differentiate `sqrt(1+x)` on a certified interval | algebraic identities; interval representations | `AlgebraicFunctions`, `AlgebraicNumbers` |
| 19 | A rational circle approximation algorithm | compute a certified point/arc enclosure at stage `n` | executable rational arithmetic; error modulus | `RationalCircle`, `ComplexInterval` |
| 20 | A computable continuity/extension problem | extend a rational function from a certified dense domain | explicit moduli; quotient/interval representations | `Extension`, `FunctionDomains` |

## Selection criteria

These are intended to be applications, not isolated identities. Each should
have:

1. a concrete input, output, or decision problem;
2. at least one proof that can be checked locally in Lean;
3. a meaningful dependency boundary, so imported theorems can remain
   black-boxes while their own proof routes are explored separately;
4. at least one alternate route—geometric, algebraic, series-based, ODE-based,
   or computable-analytic—when mathematically appropriate.

The first wave should be 1, 3, 5, 7, 10, 12, 13, 16, 18, and 19.  These give
the network early coverage across trigonometry, geometry, integration, series,
ODEs, algebraic functions, and executable approximation.
