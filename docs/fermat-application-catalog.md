# Application catalog: the first twenty problems

These are theorem-sized applications for math-net.  The small arithmetic
identities in `Benchmarks.lean` are examples used to introduce the ideas; the
items below are intended to be genuine problems with alternative proof routes.

| # | Application/problem | Main mathematical content | Candidate Lean routes |
|---:|---|---|---|
| 1 | Decide whether a factored `n` is a sum of two squares | Prime-factor criterion | elementary congruences; Gaussian integers |
| 2 | Compute `r₂(n)` from a factorization | Representation-count formula | divisors; Dirichlet character mod 4 |
| 3 | Enumerate all representations and certify the `r₂(n)` count | Algorithm/proof correspondence | finite search; factorization theorem |
| 4 | Determine when a prime representation is unique up to signs/order | Uniqueness for prime norms | Euclid's lemma; Gaussian factorization |
| 5 | Compose representations of `m` and `n` into one of `mn` | Brahmagupta–Fibonacci identity | pair algebra; rotation matrices |
| 6 | Recover a representation of a composite from Gaussian factors | Norm descent | Euclidean algorithm; gcd in `ℤ[i]` |
| 7 | Produce rational points on the unit circle from a sum-of-squares witness | Stereographic/lattice geometry | rational arithmetic; circle identities |
| 8 | Produce a Pythagorean triple with a prescribed hypotenuse | Circle points and integer scaling | parametrization; factorization |
| 9 | Prove that no integer right triangle has square area | Fermat infinite descent | elementary number theory; descent |
| 10 | Prove the equivalent prime obstruction for `p ≡ 3 mod 4` | Odd-prime divisors of a square | modular arithmetic; Euclid's lemma |
| 11 | Compare the elementary and Gaussian proofs of the prime theorem | Proof-route comparison | local Lean proof vs imported UFD results |
| 12 | Formalize the four-square composition identity | Norm composition beyond `ℤ[i]` | quaternions; polynomial algebra |
| 13 | Decide whether a rational circle point has an integer lift | Denominator and primitive-vector arithmetic | gcd; Pythagorean parametrization |
| 14 | Count primitive representations separately from imprimitive ones | Möbius/divisor structure | finite arithmetic; multiplicativity |
| 15 | Establish the finite rotation law for rational slopes | Tangent addition as coordinate composition | computable-analysis rational-circle API |
| 16 | Give a geometric proof of a concrete norm-composition problem | Angles, circles, and lattice vectors | arctangent geometry; rational circle |
| 17 | Prove a Machin-style arctangent identity from the rotation law | A transcendental-facing application | computable-analysis arctangent presentations |
| 18 | Connect the arctangent identity to a certified representation of `π` | Branches and angle normalization | geometric arctan; series/integral bridges |
| 19 | Compare `π` representations without making Euler's identity definitional | Dependency-boundary benchmark | imported exp/log or rotation foundations |
| 20 | Build an interactive proof/application lesson for Fermat's theorem | Pedagogical orchestration | theorem node; selectable proof records; dependency view |

The first implementation wave should target 1–5, 7–10, and 15–18.  Items
11–14 and 19–20 organize the network and comparison layers; they need not all
be completed before the first benchmark lesson is useful.

## Proof-status policy

Each application may have several Lean proof records.  A proof can be locally
kernel-checked while treating deeper theorems as black boxes.  The application
status therefore records both local checking and recursive dependency closure.
The graph should display the selected proof's dependencies, not turn every
proof record into a permanent node.
