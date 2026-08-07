import MathNetwork.Fermat.Registry
import MathNetwork.Euler.Applications

open MathNetwork.Fermat

#eval availableRoutes
#eval MathNetwork.Euler.applicationCatalogue

example : fermatPrimeTwoSquares := gaussianEuclideanRoute.proof
example : fermatPrimeTwoSquares := zagierInvolutionRoute.proof
example {p : Nat} (h : Fact p.Prime) (hp : p % 4 = 1) :
    ∃ a b : Nat, a ^ 2 + b ^ 2 = p := fermat_two_squares_gaussian h hp
example {p : Nat} (h : Fact p.Prime) (hp : p % 4 = 1) :
    ∃ a b : Nat, a ^ 2 + b ^ 2 = p := fermat_two_squares_involution h hp

def main : IO Unit :=
  IO.println "Fermat proof routes registered."
