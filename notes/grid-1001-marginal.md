## 1001 by 1001 grid at q = 1009

Delete a horizontal line. Each affine row or column has 1009 points. Within the selected grid each line has eight private points, 1001 ordinary crossings and one point at infinity. All choices of a deleted line are equivalent under relabelling of the incidence function. Let delta be the cost of a minimum monotone binary circuit before deletion minus the cost after deletion.

| Horizontal infinity input | Vertical infinity input | Delta |
| --- | --- | ---: |
| free | free | between 10 and 1011 |
| 0 | free | at least 11 |
| free | 0 | at least 12 |
| 0 | 0 | exactly 1010 |
| 1 | free | exactly 1 |
| free | 1 | exactly 1011 |

For the zero restrictions, each line still has private points. Apply the active-point plus distinct-neighbourhood lower bound before deletion and the row upper bound after deletion. A remaining hub on 1001 lines costs 999 in the budget. With both hubs removed the row bounds are tight on both sides. The exact affine costs are 2022019 and 2021009. With both hubs present the respective intervals are [2022023,2024021] and [2021013,2023010]. These intervals are bounds on two independent minima.

For horizontal hub = 1, the deleted horizontal contributes only its selector, an independent variable ORed with the surviving function. Pinning the selector off saves at least one gate; appending one OR gate is sufficient. For vertical hub = 1, all column selectors enter as free OR terms. All 1009 affine bits on the deleted horizontal now occur only with its selector. Pin 1008 of them false for one gate apiece. Both phases of the last bit are nonconstant, so expensive_phase gives two more gates. The horizontal selector is still essential in both phases (use the horizontal hub), and pinning it off saves one more. The reverse construction takes 1009 binary ORs, one AND and one output OR. The unrestricted 10 bound uses the same argument with eight private points. These marginal applications are paper arguments. The accompanying script checks multiplicities at full scale and Boolean identities on the 2 by 2 analogue, not minimum circuits by enumeration.

Subtract the exact affine costs from the original minima. The unrestricted delta equals ten exactly when the excess after deletion exceeds the excess before deletion by 1000. It is at least eleven exactly when the excess increases by at most 999. A lower bound of 2023021 before deletion or an upper bound of 2022012 after deletion would already suffice. No such bound or counterexample is established here.
