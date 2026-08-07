# Euler applications: application-first benchmark cards

Euler's identity should first appear as a useful calculus tool.  The proof
network can then compare the complex-exponential route with a real-variable
route that avoids Euler's identity.

## 1. Trigonometric addition identities

Benchmark:

\[
  \cos(x+y)=\cos x\cos y-\sin x\sin y,
  \qquad
  \sin(x+y)=\sin x\cos y+\cos x\sin y.
\]

Proof records:

- **Euler route:** multiply `exp(ix)` and `exp(iy)`, then compare real and
  imaginary parts.
- **Real route:** use angle addition from circle geometry or the rotation
  matrix law.

Concrete application: simplify a phase-shifted sinusoid or rotate a planar
vector.

## 2. Integrals of trigonometric functions

Benchmark:

\[
  \int e^{ax}\cos(bx)\,dx,
  \qquad
  \int e^{ax}\sin(bx)\,dx.
\]

Proof records:

- **Euler route:** take the real and imaginary parts of
  `∫ exp((a+ib)x) dx`.
- **Real route:** use an undetermined linear combination of
  `e^{ax}\cos(bx)` and `e^{ax}\sin(bx)`, followed by differentiation.

Concrete application: compute the response of a damped sinusoidal signal.

## 3. Constant-coefficient linear ODEs

Benchmark:

\[
  y''+2ay'+(a^2+b^2)y=0.
\]

Proof records:

- **Euler route:** solve the characteristic equation with roots `-a ± ib`.
- **Real route:** rewrite the equation as a two-dimensional real system and
  solve it using a rotation-dilation matrix.

Concrete application: damped oscillators and RLC circuits.

## 4. Fourier series and transforms

Benchmark: represent a real periodic signal using complex coefficients

\[
  f(x)=\sum_{n\in\mathbb Z} c_n e^{inx}
\]

instead of separately carrying sine and cosine coefficients.

Proof records:

- **Euler route:** one exponential basis and one coefficient family.
- **Real route:** separate sine and cosine bases, with explicit conversion
  between the two coefficient systems.

Concrete application: filtering or phase-shifting a real signal.

## Network design

Each application is one theorem/application node with attached proof records:

```text
Fourier signal reconstruction
├── Euler-complex proof
│   ├── Euler bridge
│   ├── complex multiplication
│   └── exponential/rotation dependencies
└── real trigonometric proof
    ├── sine/cosine orthogonality
    ├── real addition identities
    └── coefficient conversion
```

The first screen should show the application and its two methods.  Only after
selecting a method should the dependency tree expand.  This preserves the
calculus-teaching order: usefulness first, foundations second.
