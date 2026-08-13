import MathNetwork.Comparisons.IrrationalSqrtTwo
import MathNetwork.Comparisons.MathlibIrrationalSqrt
import MathNetwork.Comparisons.ComputableIrrationalSqrt

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
  routes : List (String × String)

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

def all : List CheckedComparison := [irrationalSqrtTwo]

/-- The two general irrational-square-root criteria are the same comparison
question over Mathlib's completed reals and computable-analysis raw reals.
The graph keeps their routes together while making the missing real-number
bridge explicit. -/
def irrationalSqrtRat : FoundationAlignedComparison where
  id := "irrational-sqrt-rational"
  note := "Foundation-aligned declarations: Mathlib uses ℝ and computable-analysis uses RealRaw. A checked representation bridge is required before Lean can identify their proposition types."
  routes := [
    ("mathlib", "MathNetwork.MathlibSqrt.irrational_sqrt_ratCast_iff_of_nonneg"),
    ("computable-analysis", "MathNetwork.ComputableSqrt.irrational_sqrt_ratCast_iff_of_nonneg")
  ]

def aligned : List FoundationAlignedComparison := [irrationalSqrtRat]

end MathNetwork.Comparisons
