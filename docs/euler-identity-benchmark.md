# Euler identity as a proof-comparison benchmark

The baseline identity

\[
  e^{i\pi}+1=0
\]

is too easy if `exp`, `sin`, and `cos` are all introduced by mutually
coordinated power series. math-net should therefore treat it as a bridge
between independently meaningful constructions.

## Common statement

Use the circle-derived value of `π`, the geometric or rotation-derived
functions `sin` and `cos`, and an independently constructed complex
exponential. The target is the family

\[
  \exp(i\theta)=\cos\theta+i\sin\theta,
  \qquad \exp(i\pi/2)=i,
  \qquad \exp(i\pi)=-1.
\]

The last equality is the viral statement; the quarter-turn equality is the
more useful benchmark because it exposes the circle connection directly.

## Concrete application

Apply the quarter-turn to a nontrivial lattice vector:

\[
  \exp(i\pi/2)(3+4i)=-4+3i.
\]

The norm is preserved, and the result is the geometric 90-degree rotation of
the `3–4–5` vector. This forces the identity to do mathematical work rather
than merely restate the definitions of the functions.

## Proof records

1. **Power-series baseline.** A deliberately easy reference proof using
   coordinated power-series definitions.
2. **ODE uniqueness.** Construct `exp` from `f' = f` and `sin/cos` from the
   rotation system `C' = -S`, `S' = C`; prove the bridge by uniqueness.
3. **Geometric rotation.** Construct the unit-circle quarter-turn and connect
   it to the independently constructed exponential.
4. **Computable route.** Use finite rational rotation prefixes and explicit
   error certificates, then establish the represented complex equality.

Each route should expose whether `π`, rotation, and exponential are imported
black boxes or recursively expanded in the dependency network.
