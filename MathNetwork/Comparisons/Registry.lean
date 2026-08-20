import MathNetwork.Comparisons.IrrationalSqrtTwo
import MathNetwork.Comparisons.MathlibIrrationalSqrt
import MathNetwork.Comparisons.ComputableIrrationalSqrt
import MathNetwork.Comparisons.ComputableFTC
import MathNetwork.Comparisons.ComputableFourier
import MathNetwork.Comparisons.ComputableSeries
import MathNetwork.Comparisons.ComputableDeMoivre
import MathNetwork.Comparisons.ComputablePiGeometry
import MathNetwork.Comparisons.ComputableLogarithm
import MathNetwork.Comparisons.ComputableNilakantha
import MathNetwork.Fermat.Registry
import MathNetwork.Euler.Applications
import MathNetwork.Euler.Identity

/-!
# Checked proposition comparisons

This file records comparison units whose routes have literally the same
checked Lean proposition.  The computable square-root criterion is indexed as
a separate native-representation declaration until its explicit bridge to
Mathlib's completed real numbers is formalized.
-/

namespace MathNetwork.Comparisons

structure CheckedProof (statement : Prop) where
  repository : String
  declaration : String
  title : String
  description : String
  proof : statement

structure CheckedComparison where
  id : String
  title : String
  description : String
  area : String := "General mathematics"
  statement : Prop
  routes : List (CheckedProof statement)

/-- A visual alignment between checked declarations expressed over different
foundations.  Unlike `CheckedComparison`, this does not assert definitional
equality: a separately checked representation bridge is required before the
two declarations can become one Lean proposition. -/
structure FoundationAlignedComparison where
  id : String
  title : String
  description : String
  note : String
  mathematicalCore : String
  routes : List (String × String × String)

def irrationalSqrtTwo : CheckedComparison where
  id := "irrational-sqrt-two"
  title := "Irrationality of √2"
  description := "A concrete corollary whose upstream criterion is compared separately across real-number foundations."
  statement := Irrational (√2)
  routes := [
    {
      repository := "mathlib"
      declaration := "MathNetwork.SqrtTwo.irrational"
      title := "Mathlib irrational-square-root theorem"
      description := "A checked Mathlib corollary for the concrete benchmark √2."
      proof := MathNetwork.SqrtTwo.irrational
    }
  ]

/-- Fermat's two-square theorem is the first full exact-proof comparison:
the Gaussian-integer result supplied by Mathlib and the locally assembled
Zagier involution proof establish precisely the same Lean proposition. -/
def fermatTwoSquares : CheckedComparison where
  id := "fermat-prime-two-squares"
  title := "Fermat's two-square theorem"
  description := "Every prime congruent to 1 modulo 4 is a sum of two squares, with Gaussian-integer and involution proofs."
  statement := MathNetwork.Fermat.fermatPrimeTwoSquares
  routes := [
    {
      repository := "mathlib"
      declaration := "MathNetwork.Fermat.fermat_two_squares_gaussian"
      title := "Gaussian integers"
      description := "Mathlib's prime-as-a-sum-of-two-squares theorem through the Gaussian-integer Euclidean domain."
      proof := MathNetwork.Fermat.fermat_two_squares_gaussian
    },
    {
      repository := "math-net"
      declaration := "MathNetwork.Fermat.fermat_two_squares_involution"
      title := "Zagier involution"
      description := "A fixed-point parity argument with two involutions on a finite set."
      proof := MathNetwork.Fermat.fermat_two_squares_involution
    }
  ]

/-- Euler's identity is used here as an actual proof mechanism: take real and
imaginary parts of the exponential addition law, rather than treating the
addition formulas as definitions. -/
def cosineAddition : CheckedComparison where
  id := "cosine-addition"
  title := "Cosine addition formula"
  description := "The standard real-trigonometric formula, compared with a derivation from complex exponentials."
  statement := ∀ x y : ℝ,
    Real.cos (x + y) = Real.cos x * Real.cos y - Real.sin x * Real.sin y
  routes := [
    {
      repository := "mathlib"
      declaration := "Real.cos_add"
      title := "Real trigonometry"
      description := "Mathlib's standard real sine-and-cosine addition theorem."
      proof := Real.cos_add
    },
    {
      repository := "math-net"
      declaration := "MathNetwork.Euler.trig_addition_euler_cos_route"
      title := "Complex exponential"
      description := "Take the real part of exp((x + y)i) = exp(xi) exp(yi)."
      proof := MathNetwork.Euler.trig_addition_euler_cos_route
    }
  ]

def sineAddition : CheckedComparison where
  id := "sine-addition"
  title := "Sine addition formula"
  description := "The standard real-trigonometric formula, compared with a derivation from complex exponentials."
  statement := ∀ x y : ℝ,
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y
  routes := [
    {
      repository := "mathlib"
      declaration := "Real.sin_add"
      title := "Real trigonometry"
      description := "Mathlib's standard real sine-and-cosine addition theorem."
      proof := Real.sin_add
    },
    {
      repository := "math-net"
      declaration := "MathNetwork.Euler.trig_addition_euler_sin_route"
      title := "Complex exponential"
      description := "Take the imaginary part of exp((x + y)i) = exp(xi) exp(yi)."
      proof := MathNetwork.Euler.trig_addition_euler_sin_route
    }
  ]

/-- A finished computable-analysis application that is useful in its own
right, even before a Mathlib representation bridge identifies it with a
completed-real series limit. -/
def telescopingReciprocalSeries : CheckedComparison where
  id := "telescoping-reciprocal-series"
  title := "Telescoping reciprocal series"
  description := "A certified rational-interval computation of the exact value of the reciprocal triangular series."
  area := "Series"
  statement := ComputableAnalysis.Series.triangularTelescopingRaw.Equiv
    (ComputableAnalysis.RealRaw.ofRat 2)
  routes := [
    {
      repository := "computable-analysis"
      declaration := "MathNetwork.ComputableSeries.triangularTelescopingRaw_equiv_two"
      title := "Certified telescoping intervals"
      description := "Finite rational partial sums give nested intervals converging to 2."
      proof := MathNetwork.ComputableSeries.triangularTelescopingRaw_equiv_two
    }
  ]

/-- The new certified connection between the alternating-series and
power-series presentations of sine. It is intentionally retained as a
single-route presentation until a matching theorem is transported from a
second foundation. -/
def sineTaylorIntervalBridge : CheckedComparison where
  id := "sine-alternating-taylor-bridge"
  title := "Sine: alternating series and Taylor intervals"
  description := "A checked identification of the computable alternating-series enclosure with the corresponding sine Taylor partial-sum interval."
  area := "Trigonometry and series"
  statement := ∀ {x : Rat} (hx : 0 <= x) (hterms : ComputableAnalysis.qabs x <= 2) (n : Nat),
    (ComputableAnalysis.Series.AlternatingRaw.sineAlternatingRaw x hterms).interval n =
      ComputableAnalysis.Series.evenOddInterval
        (ComputableAnalysis.FormalPowerSeries.sineTaylorPartial x) n
  routes := [
    {
      repository := "computable-analysis"
      declaration := "MathNetwork.ComputableSeries.sineAlternatingRaw_interval_eq_sineTaylorInterval"
      title := "Alternating-series/Taylor bridge"
      description := "The finite interval enclosure is proved identical to the Taylor partial-sum enclosure on the controlled input range."
      proof := MathNetwork.ComputableSeries.sineAlternatingRaw_interval_eq_sineTaylorInterval
    }
  ]

def finiteDeMoivre : CheckedComparison where
  id := "finite-de-moivre-rational-circle"
  title := "Finite De Moivre on the rational circle"
  description := "Taking a natural power commutes with multiplication of rational unit-circle points: a geometric form of De Moivre without angles, exp, or completed complex numbers."
  area := "Geometry and algebra"
  statement := ∀ (p q : ComputableAnalysis.PiCirclePoint) (n : Nat),
    ComputableAnalysis.RationalCircle.Trigonometry.pointPow
      (ComputableAnalysis.RationalCircle.Trigonometry.pointMul p q) n =
      ComputableAnalysis.RationalCircle.Trigonometry.pointMul
        (ComputableAnalysis.RationalCircle.Trigonometry.pointPow p n)
        (ComputableAnalysis.RationalCircle.Trigonometry.pointPow q n)
  routes := [
    {
      repository := "computable-analysis"
      declaration := "MathNetwork.ComputableDeMoivre.pointPow_mul"
      title := "Rational-circle powers"
      description := "A finite rational-coordinate rotation identity, with no analytic limit or angle convention in the statement."
      proof := MathNetwork.ComputableDeMoivre.pointPow_mul
    }
  ]

/-- The canonical complex-exponential identity is an application landmark in
its own right. A second foundation can later be added as a route to this same
statement once a checked complex-number bridge is available. -/
def eulerIdentity : CheckedComparison where
  id := "euler-identity"
  title := "Euler's identity"
  description := "The complex exponential at πi is −1: a central landmark whose downstream uses include trigonometric identities, differential equations, and Fourier analysis."
  area := "Complex analysis and trigonometry"
  statement := Complex.exp ((Real.pi : ℂ) * Complex.I) = -1
  routes := [
    {
      repository := "mathlib"
      declaration := "MathNetwork.Euler.exp_pi_mul_I"
      title := "Complex exponential"
      description := "Mathlib's checked complex-exponential theorem, presented under a stable landscape declaration."
      proof := MathNetwork.Euler.exp_pi_mul_I
    }
  ]

/-- A finite, exact Fourier application.  This is deliberately presented as a
four-point rational-coordinate theorem rather than as an infinite-transform
or completeness result. -/
def fourPointParseval : CheckedComparison where
  id := "four-point-parseval"
  title := "Four-point Parseval identity"
  description := "The unnormalised four-point Fourier transform preserves energy up to the factor four, over exact rational coordinates."
  area := "Fourier analysis"
  statement := ∀ (x₀ x₁ x₂ x₃ : Rat),
    ComputableAnalysis.QComplex.normSq
        (ComputableAnalysis.fourPointFourierTransform x₀ x₁ x₂ x₃ 0) +
        ComputableAnalysis.QComplex.normSq
          (ComputableAnalysis.fourPointFourierTransform x₀ x₁ x₂ x₃ 1) +
        ComputableAnalysis.QComplex.normSq
          (ComputableAnalysis.fourPointFourierTransform x₀ x₁ x₂ x₃ 2) +
        ComputableAnalysis.QComplex.normSq
          (ComputableAnalysis.fourPointFourierTransform x₀ x₁ x₂ x₃ 3) =
      4 * (x₀ ^ 2 + x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2)
  routes := [
    {
      repository := "computable-analysis"
      declaration := "MathNetwork.ComputableFourier.fourPointFourierTransform_parseval"
      title := "Exact rational four-point transform"
      description := "A checked finite Fourier energy identity using the rational quarter-turn roots."
      proof := MathNetwork.ComputableFourier.fourPointFourierTransform_parseval
    }
  ]

/-- A direct geometry-to-arctangent bridge for π, without the broader π
presentation registry. -/
def piCircleAreaGeometricArctangent : CheckedComparison where
  id := "pi-circle-area-geometric-arctangent"
  title := "π: circle area equals four geometric arctangents"
  description := "The circle-area algorithm and four unit geometric arctangent sectors are certified to represent the same computable real number π."
  area := "Geometry and trigonometry"
  statement :=
    (((4 : Nat) * ComputableAnalysis.ArctanGeometry.arctanGeom (1 : Rat) :
      ComputableAnalysis.RealRaw).Equiv ComputableAnalysis.piCircleArea)
  routes := [
    {
      repository := "computable-analysis"
      declaration := "MathNetwork.ComputablePiGeometry.four_arctanGeom_one_equiv_piCircleArea"
      title := "Circle area and geometric arctangent"
      description := "A stagewise rational-box equivalence between a circle-area π construction and four unit arctangent sectors."
      proof := MathNetwork.ComputablePiGeometry.four_arctanGeom_one_equiv_piCircleArea
    }
  ]

/-- A power-series/integral comparison for a basic logarithmic value. -/
def logTwoSeriesReciprocalIntegral : CheckedComparison where
  id := "log-two-series-reciprocal-integral"
  title := "log 2: alternating series equals reciprocal integral"
  description := "The alternating harmonic series and the certified reciprocal integral of 1/x on [1,2] represent the same computable real number."
  area := "Calculus and series"
  statement :=
    ComputableAnalysis.Logarithm.logTwoSeries.Equiv
      ComputableAnalysis.Logarithm.logTwoReciprocalIntegral
  routes := [
    {
      repository := "computable-analysis"
      declaration := "MathNetwork.ComputableLogarithm.logTwoSeries_equiv_logTwoReciprocalIntegral"
      title := "Alternating series and Darboux integral"
      description := "A common dyadic refinement proves overlap between the alternating-harmonic series boxes and the reciprocal-integral boxes."
      proof := MathNetwork.ComputableLogarithm.logTwoSeries_equiv_logTwoReciprocalIntegral
    }
  ]

/-- A whole-series comparison for π, rather than a finite numerical
cross-check: Nilakantha's accelerated alternating series is certified to
represent the same computable real as the classical Leibniz series. -/
def nilakanthaLeibnizPi : CheckedComparison where
  id := "nilakantha-leibniz-pi"
  title := "π: Nilakantha series equals Leibniz series"
  description := "Two infinite rational alternating-series algorithms for π are proved equivalent by termwise finite rational bounds."
  area := "Series and π"
  statement :=
    ComputableAnalysis.piNilakantha.Equiv ComputableAnalysis.piLeibniz
  routes := [
    {
      repository := "computable-analysis"
      declaration := "MathNetwork.ComputableNilakantha.nilakantha_equiv_leibniz"
      title := "Nilakantha and Leibniz alternating series"
      description := "A termwise rational comparison transports the accelerated Nilakantha enclosure to the classical Leibniz enclosure at every requested precision."
      proof := MathNetwork.ComputableNilakantha.nilakantha_equiv_leibniz
    }
  ]

def all : List CheckedComparison :=
  [irrationalSqrtTwo, fermatTwoSquares, cosineAddition, sineAddition]

/-- Checked single-route applications belong in the landscape too. They are
not comparisons until a second route has been bridged to the same checked
statement. -/
def presentations : List CheckedComparison :=
  [telescopingReciprocalSeries, sineTaylorIntervalBridge, finiteDeMoivre,
    eulerIdentity, fourPointParseval, piCircleAreaGeometricArctangent]
    ++ [logTwoSeriesReciprocalIntegral, nilakanthaLeibnizPi]

/-- The two general irrational-square-root criteria are the same comparison
question over Mathlib's completed reals and computable-analysis raw reals.
The graph keeps their routes together while making the missing real-number
bridge explicit. -/
def irrationalSqrtRat : FoundationAlignedComparison where
  id := "irrational-sqrt-rational"
  title := "Irrational square roots of rational numbers"
  description := "The shared rational-square criterion, compared over completed and computable real-number representations."
  note := "The shared mathematical core is the rational-square criterion. Mathlib uses ℝ and computable-analysis uses RealRaw for the two analytic branches; a checked representation bridge is still required before Lean can identify their irrationality predicates."
  mathematicalCore := "MathNetwork.RationalSquares.isSquare_iff_computableIsSquare"
  routes := [
    ("mathlib", "MathNetwork.MathlibSqrt.irrational_sqrt_ratCast_iff_of_nonneg", "Real"),
    ("computable-analysis", "MathNetwork.ComputableSqrt.irrational_sqrt_ratCast_iff_of_nonneg", "ComputableAnalysis.RealRaw")
  ]

def effectiveFundamentalTheorem : FoundationAlignedComparison where
  id := "effective-fundamental-theorem-of-calculus"
  title := "Fundamental theorem of calculus"
  description := "Integral of a derivative equals an endpoint difference, viewed through standard and computable-real formulations."
  note := "Both routes express the fundamental theorem—an integral of a derivative equals an endpoint difference—but Mathlib uses interval integrals over completed real numbers while computable-analysis uses certified rational interval algorithms. A representation bridge is required before Lean can merge them."
  mathematicalCore := "integral of derivative = endpoint difference"
  routes := [
    ("mathlib", "MathNetwork.List100.fundamentalTheoremOfCalculus", "Real / intervalIntegral"),
    ("computable-analysis", "MathNetwork.ComputableFTC.effectiveFTC_equiv_endpoint", "ComputableAnalysis.RealRaw")
  ]

def aligned : List FoundationAlignedComparison :=
  [irrationalSqrtRat, effectiveFundamentalTheorem]

end MathNetwork.Comparisons
