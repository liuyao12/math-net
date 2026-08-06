import MathNetwork.Fermat.Basic
import MathNetwork.Fermat.Zagier

namespace MathNetwork.Fermat

/-- A named proof route for one proposition. The proposition is stored in the
type, while the label and description make proof-family metadata queryable. -/
structure ProofRoute (P : Prop) where
  name : String
  description : String
  proof : P

def normComposition : Prop :=
  ∀ z w : GaussianPair, (z.mul w).normSq = z.normSq * w.normSq

def pairAlgebraRoute : ProofRoute normComposition :=
  { name := "pair-algebra"
    description := "Direct integer algebra on Gaussian pairs; no completeness."
    proof := normSq_mul }

/-- The concrete Fermat witness is kept as a separate target from the general
two-square theorem, so computations do not disappear into a large theorem. -/
def witness29 : Prop := ∃ a b : Int, a * a + b * b = 29

def witness29Route : ProofRoute witness29 :=
  { name := "explicit-witness"
    description := "A certified finite witness for 29 = 5^2 + 2^2."
    proof := by
      refine ⟨5, 2, ?_⟩
      norm_num }

def fermatPrimeTwoSquares : Prop :=
  ∀ {p : Nat}, Fact p.Prime → p % 4 = 1 →
    ∃ a b : Nat, a ^ 2 + b ^ 2 = p

def zagierInvolutionRoute : ProofRoute fermatPrimeTwoSquares :=
  { name := "zagier-involution"
    description :=
      "Two involutions on a finite set; the local theorem assembles the parity argument."
    proof := by
      intro p hp hmod
      exact @fermat_two_squares_involution p hp hmod }

def availableRoutes : List String :=
  [pairAlgebraRoute.name, witness29Route.name, "involution-fixed-point",
   zagierInvolutionRoute.name, "geometric-lattice", "gaussian-euclidean"]

end MathNetwork.Fermat
