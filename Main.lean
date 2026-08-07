import MathNetwork.Fermat.Registry
import MathNetwork.Euler.Applications

open MathNetwork.Fermat

#eval availableRoutes
#eval MathNetwork.Euler.applicationCatalogue

example : normComposition := pairAlgebraRoute.proof
example : witness29 := witness29Route.proof
example : isSumOfTwoSquares 13 := sumSquares_13
example : ¬ isSumOfTwoSquares 7 := not_sumSquares_7
example : 3 ^ 2 + 4 ^ 2 = 5 ^ 2 := pythagorean_3_4_5

def main : IO Unit :=
  IO.println "Fermat proof routes registered."
