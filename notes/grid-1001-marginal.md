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

### Restoring the crossings of one row

Keep both infinity bits free. Fix to zero all but k of the 1001 crossing point bits on a chosen horizontal line. Let D(k) and E(k) be the exact minimum costs before and after deleting the line in that restricted function. Permuting the columns shows these costs depend only on k. Other rows, all private bits, and both hubs remain available.

E(k) = E(0)+k: after deletion each restored bit is a twin of an existing private point of its column. One OR suffices to add a twin and pinning an essential bit false saves at least one gate. At k=0 the deleted row has eight private bits and just the horizontal hub in common with other rows. The eight-private-point lower bound saves ten. A row term on nine point bits can be appended in exactly ten gates, so D(0)=E(0)+10.

One restoration increases D by at least one via essentiality, and at most three: append the OR of the row and column selectors, its AND with the restored bit, and an output OR. Thus the unrestricted marginal equals 10 plus the sum over k=1,...,1001 of D(k)-D(k-1)-1. All summands are 0, 1 or 2. A single strict increment at any stage settles the 11-gate target. Exact ten forces every increment to be one. The arithmetic endpoint criterion and a circuit-level reader obstruction are proved in PrivateGridMarginal.lean; their geometric instantiation here is on paper.

In particular, if the original marginal equals ten, choose any crossing and restore it last on its row. Pinning it false then reduces the optimum by exactly one. In every least clean monotone circuit it has exactly one direct reader and that reader is an OR. Two readers, or one AND reader and its live successor, would save at least two. This applies to all 1002001 crossings at once by symmetry. No two of their readers coincide: the two sole inputs to the same OR would be interchangeable, whereas two different crossings have distinct row/column neighbourhoods.

Moreover the other input to each such OR must be zero on every singleton assignment. It is independent of the crossing bit by acyclicity and sole readership. If it fired on a point singleton different from the crossing, select one of the two lines through the crossing missing that point. Toggling the crossing changes the target but cannot change its OR reader. If it fired on a selector singleton, turn on all selectors and no points for the same contradiction. The crossing singleton itself reduces to the all-zero assignment for the partner. Consequently the partner cannot be an OR-only expression of raw inputs. It must also fire on some incident point-selector pair without that crossing: otherwise bypassing the OR by the raw crossing preserves every minimal true assignment and can only decrease the computed function, contradicting minimality. These conditions do not imply distinct partner wires.

There must also be an AND downstream of each crossing reader, since an OR-only path to the output would accept the crossing singleton. Thus circuits with at most one AND per input-output path cannot witness exact ten. This leaves general circuits with nested ANDs.
