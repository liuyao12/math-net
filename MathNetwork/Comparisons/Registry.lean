import MathNetwork.Comparisons.IrrationalSqrtTwo
import MathNetwork.Comparisons.MathlibIrrationalSqrt
import MathNetwork.Comparisons.ComputableIrrationalSqrt
import MathNetwork.Comparisons.ComputableFTC
import MathNetwork.Comparisons.ComputableFourier
import MathNetwork.Fermat.Registry

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
  proof : statement

structure CheckedComparison where
  id : String
  statement : Prop
  routes : List (CheckedProof statement)

/-- A visual alignment between checked declarations expressed over different
foundations.  Unlike `CheckedComparison`, this does not assert definitional
equality: a separately checked representation bridge is required before the
two declarations can become one Lean proposition. -/
structure FoundationAlignedComparison where
  id : String
  note : String
  mathematicalCore : String
  routes : List (String × String × String)

def irrationalSqrtTwo : CheckedComparison where
  id := "irrational-sqrt-two"
  statement := Irrational (√2)
  routes := [
    {
      repository := "mathlib"
      declaration := "MathNetwork.SqrtTwo.irrational"
      proof := MathNetwork.SqrtTwo.irrational
    }
  ]

/-- Fermat's two-square theorem is the first full exact-proof comparison:
the Gaussian-integer result supplied by Mathlib and the locally assembled
Zagier involution proof establish precisely the same Lean proposition. -/
def fermatTwoSquares : CheckedComparison where
  id := "fermat-prime-two-squares"
  statement := MathNetwork.Fermat.fermatPrimeTwoSquares
  routes := [
    {
      repository := "mathlib"
      declaration := "MathNetwork.Fermat.fermat_two_squares_gaussian"
      proof := MathNetwork.Fermat.fermat_two_squares_gaussian
    },
    {
      repository := "math-net"
      declaration := "MathNetwork.Fermat.fermat_two_squares_involution"
      proof := MathNetwork.Fermat.fermat_two_squares_involution
    }
  ]

def all : List CheckedComparison := [irrationalSqrtTwo, fermatTwoSquares]

/-- The two general irrational-square-root criteria are the same comparison
question over Mathlib's completed reals and computable-analysis raw reals.
The graph keeps their routes together while making the missing real-number
bridge explicit. -/
def irrationalSqrtRat : FoundationAlignedComparison where
  id := "irrational-sqrt-rational"
  note := "The shared mathematical core is the rational-square criterion. Mathlib uses ℝ and computable-analysis uses RealRaw for the two analytic branches; a checked representation bridge is still required before Lean can identify their irrationality predicates."
  mathematicalCore := "MathNetwork.RationalSquares.isSquare_iff_computableIsSquare"
  routes := [
    ("mathlib", "MathNetwork.MathlibSqrt.irrational_sqrt_ratCast_iff_of_nonneg", "Real"),
    ("computable-analysis", "MathNetwork.ComputableSqrt.irrational_sqrt_ratCast_iff_of_nonneg", "ComputableAnalysis.RealRaw")
  ]

def effectiveFundamentalTheorem : FoundationAlignedComparison where
  id := "effective-fundamental-theorem-of-calculus"
  note := "Both routes express the fundamental theorem—an integral of a derivative equals an endpoint difference—but Mathlib uses interval integrals over completed real numbers while computable-analysis uses certified rational interval algorithms. A representation bridge is required before Lean can merge them."
  mathematicalCore := "integral of derivative = endpoint difference"
  routes := [
    ("mathlib", "MathNetwork.List100.fundamentalTheoremOfCalculus", "Real / intervalIntegral"),
    ("computable-analysis", "MathNetwork.ComputableFTC.effectiveFTC_equiv_endpoint", "ComputableAnalysis.RealRaw")
  ]

def aligned : List FoundationAlignedComparison :=
  [irrationalSqrtRat, effectiveFundamentalTheorem]

end MathNetwork.Comparisons
