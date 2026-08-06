import MathNetwork.Fermat.Registry

open MathNetwork.Fermat

#eval availableRoutes

example : normComposition := pairAlgebraRoute.proof
example : witness29 := witness29Route.proof

def main : IO Unit :=
  IO.println "Fermat proof routes registered."
