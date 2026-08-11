import MathNetwork.Comparisons.IrrationalSqrtTwo
import MathNetwork.Comparisons.IrrationalSqrtTwoDescent

/-!
# Checked proposition comparisons

This file records the comparison units that math-net hosts itself.  A
comparison does not duplicate either upstream development: it specializes the
routes to one common proposition and stores both checked proof terms against
that proposition.
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
    },
    {
      repository := "computable-analysis"
      declaration := "MathNetwork.SqrtTwo.irrational_descent"
      proof := MathNetwork.SqrtTwo.irrational_descent
    }
  ]

def all : List CheckedComparison := [irrationalSqrtTwo]

end MathNetwork.Comparisons
