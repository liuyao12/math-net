import MathNetwork.Comparisons.IrrationalSqrtTwo

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

end MathNetwork.Comparisons
