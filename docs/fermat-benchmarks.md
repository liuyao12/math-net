# Fermat examples and benchmark problems

The small calculations below are examples and Lean smoke tests, not the main
benchmark layer. The real benchmark problems ask for a mathematical decision,
count, or explanation from nontrivial arithmetic data.

| Example or problem | Lean declaration | Role |
| --- | --- | --- |
| `13 = 3² + 2²`, `17 = 4² + 1²` | `sumSquares_13`, `sumSquares_17` | Warm-up examples |
| `3` and `7` are not sums of two squares | `not_sumSquares_3`, `not_sumSquares_7` | Warm-up obstruction |
| `65 = 1² + 8² = 4² + 7²` | `two_representations_65` | Example of non-uniqueness |
| Compose `13` and `17` to obtain `221 = 10² + 11²` | `compose_13_17`, `sumSquares_221_by_composition` | Example of norm composition |
| `(5,2)` gives `(21/29,20/29)` on the unit circle | `rationalCirclePoint_5_2_on_unit_circle` | Example of geometric reinterpretation |
| `arctan(2/3)+arctan(1/4)=arctan(11/10)` | `arctan_compose_13_17` | Example for the trig route |
| Decide representability from a nontrivial prime factorization | planned | Existence benchmark |
| Compute `r₂(n)` from the factorization and explain every representation | planned | Counting benchmark |
| Compare the factorization count with an explicit enumerator | planned | Computation/proof correspondence |
| No integer right triangle has square area | planned | Infinite descent and a deeper Fermat application |

The factorization and `r₂` rows are the intended first serious application
benchmarks; the concrete rows support their pedagogy and regression testing.
