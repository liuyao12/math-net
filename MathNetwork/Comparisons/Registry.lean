import MathNetwork.Comparisons.IrrationalSqrtTwo
import MathNetwork.Comparisons.MathlibIrrationalSqrt
import MathNetwork.Comparisons.ComputableIrrationalSqrt
import MathNetwork.Comparisons.ComputableFTC
import MathNetwork.Comparisons.ComputableFourier
import MathNetwork.Comparisons.ComputableSeries
import MathNetwork.Fermat.Registry
import MathNetwork.Euler.Applications

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

def all : List CheckedComparison :=
  [irrationalSqrtTwo, fermatTwoSquares, cosineAddition, sineAddition,
    telescopingReciprocalSeries]

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
