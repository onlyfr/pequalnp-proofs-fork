# Deleting one line of the full arc

Let s ≥ 3. The full arc has one private input u_i per line and a shared input x_ij per unordered pair. Its function is the OR of u_i AND y_i and x_ij AND (y_i OR y_j). Let D be its minimum monotone binary circuit size; let E be the minimum after deleting one line. Permuting line labels permutes all the point inputs, so E is independent of the deleted line. All costs here count gates, allow fan-out and use one output.

## An exact comparison of the two line cofactors

Write C for the minimum cost of the canonical arc on s-1 lines, with just one private input on each. Then E = C + (s-1): deletion leaves the pair u_j, x_lj interchangeable at each surviving line j. Replacing each canonical private input by the OR of that pair constructs the upper bound. Conversely pinning x_lj to zero one by one saves at least one gate each and leaves the canonical function. Every pinned input is essential immediately before it is pinned (test with y_j alone); every intermediate restriction is nonconstant. An unused input can be set to zero and constants propagated without increasing minimum size.

Choose a line l and any k ≤ s-2 of its incident shared inputs. Pin these k crossings and u_l to zero, and denote the remaining function by H. Write H_b for its restriction at y_l=b.

* H_0 retains s-1-k pairs of interchangeable private inputs. The same pin-and-rebuild argument gives cost C+s-1-k.
* H_1 has the canonical function on the other lines ORed with s-1-k fresh free point inputs. Adding those ORs gives an upper bound, and pinning those essential free inputs to zero one by one gives the reverse inequality.

Thus **both cofactors have cost E-k**. The line input is still essential because at least one crossing survives. Both cofactors are nonconstant. For any minimum circuit for H some phase of y_l saves at least two gates: take any direct reader, use its absorbing value (zero at AND or one at OR), and remove the resulting constant reader and one live successor. The reader cannot itself be the output, since that cofactor is nonconstant. Consequently if the k+1 point pins save k+1+B gates in total, then D-E ≥ 3+B. At s=1010, **eight bonus gates on one such restriction suffice**. This is a sufficient criterion; different possible simplifications of the same gate cannot be added.

## An unconditional fourth gate

There is a point input that saves at least two gates when set to **zero**. To see this, take a minimum circuit trimmed to its output and simplify constants, unused inputs, unary gates and repeated equal operands. If any point has at least two distinct readers, zeroing it removes both readers. Otherwise every point has a unique reader. Consider the first gate in topological order that reads a point.

* At an AND gate fixing its point operand to zero also removes a live successor. The restricted function is nonconstant.
* An OR gate with two point operands would make the two singleton-point probes indistinguishable. Their line-neighborhoods in the full arc are distinct.
* At an OR gate with only one point operand, the other operand is point-free by the choice of the first gate. It is true with all lines true (a constant-free monotone circuit). Changing the point from zero to one, with all other points zero and all lines true, would leave the gate and therefore the output unchanged. The incidence function changes.

If this point is private, delete its line. The private pin gives B ≥ 1 with k=0. If it is shared, delete either incident line. Pin the shared point first at a saving of two, then pin the line's still-essential private point at a saving of at least one. This gives B ≥ 1 with k=1. Since s≥3, another crossing survives. The cofactor comparison proves **D-E ≥ 4**.

Conversely one can append the deleted row to any optimal circuit for E with s-1 OR gates to collect the row's s points, one AND with y_l, and a final OR. Thus D-E ≤ s+1. In particular the marginal is exactly four at s=3 and is in [4,1011] at s=1010. Neither endpoint at s=1010 is asserted to be attained.

## Other tests at s=1010

* Before any pin, setting u_l=true gives E OR y_l, of exact cost E+1. Setting y_l=true gives the canonical core ORed with the 1010 independent inputs in the row, also of exact cost E+1. Consequently ten distinct readers of either u_l or y_l in an optimal circuit imply D-E ≥ 11 by fixing that input to true.
* Setting y_l=false and u_l to either value computes the deletion. Eleven distinct gates in the union of their reader sets therefore suffice, even if neither input has ten readers. A shared reader counts once.
* A failed deletion would require at most seven bonus gates in **every** compatible choice/order of the point restrictions above, at most nine readers of each private or line input, and at most ten readers in each of the indicated unions, in every minimum circuit. These are necessary conditions on a counterexample, not a construction.
* Let C_j denote the cost of the canonical j-line arc. The desired decision is precisely C_1010-C_1009 ≥ 1020 versus ≤ 1019. A lower bound on C_1010 alone cannot give this comparison.

The accompanying Lean module checks the generic two-pin reader elimination and absorbing-phase elimination for the project's actual circuit model, the cofactor function identities, and the conditional inequality balanced_marginal. The transfer of the exact twin/free-input costs and the first-point argument to a single numeric theorem about the encoded 1009-plane remain paper proofs.
