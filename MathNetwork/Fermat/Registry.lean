import MathNetwork.Fermat.Basic
import MathNetwork.Fermat.Zagier
import Mathlib.NumberTheory.SumTwoSquares

namespace MathNetwork.Fermat

/-- A named proof route for one proposition. The proposition is stored in the
type, while the label and description make proof-family metadata queryable. -/
structure ProofRoute (P : Prop) where
  name : String
  description : String
  proof : P

def fermatPrimeTwoSquares : Prop :=
  ∀ {p : Nat}, Fact p.Prime → p % 4 = 1 →
    ∃ a b : Nat, a ^ 2 + b ^ 2 = p

def gaussianEuclideanRoute : ProofRoute fermatPrimeTwoSquares :=
  { name := "gaussian-euclidean"
    description := "Mathlib's maintained route through the Euclidean domain of Gaussian integers."
    proof := by
      intro p hp hmod
      apply Nat.Prime.sq_add_sq (p := p)
      omega }

def zagierInvolutionRoute : ProofRoute fermatPrimeTwoSquares :=
  { name := "zagier-involution"
    description :=
      "Two involutions on a finite set; the local theorem assembles the parity argument."
    proof := by
      intro p hp hmod
      exact @fermat_two_squares_involution p hp hmod }

def availableRoutes : List String :=
  [gaussianEuclideanRoute.name, zagierInvolutionRoute.name]

end MathNetwork.Fermat
