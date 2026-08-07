import MathNetwork.Fermat.Registry
import MathNetwork.Euler.Applications

open MathNetwork.Fermat

#eval availableRoutes
#eval MathNetwork.Euler.applicationCatalogue

example : fermatPrimeTwoSquares := gaussianEuclideanRoute.proof
example : fermatPrimeTwoSquares := zagierInvolutionRoute.proof

def main : IO Unit :=
  IO.println "Fermat proof routes registered."
