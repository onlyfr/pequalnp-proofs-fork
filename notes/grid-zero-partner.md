# Order 1009: the 1001 by 1001 grid saves at least eleven gates

This is a paper proof for the specific two-pencil grid, with both infinity bits free. The final finite-set accounting and arithmetic contradiction are Lean checked. The repository does not yet contain an end-to-end Lean theorem instantiating the circuit transformations for this grid.

## Lean status for the uncompressed grid

`PrivateGrid1009.matched_one_row` fixes a particular horizontal deletion. From a ten-gate upper bound its minimum circuit admits one injective matching of all 1,002,001 crossing readers to direct consumers. The proof keeps eight private points per line and both independent infinity inputs. Row permutations preserve the erased minimum.

`PrivateGrid1009.cuts_of_ten` uses that same matching for every subset of rows or columns. For a cut of size d the explicit restoration costs at most 2011d+1001 gates. Folding the 1001d matched consumers gives the allowance 1010d+1001. The set of readers with a touched partner and the extra matched-partner credits are computed from the actual circuit. `PrivateGrid1009.incompatible_counts` connects both cut inequalities to averaging over all subsets.

`PrivateGrid1009.first_probes` constructs both first changed consumers. `PrivateGrid1009.gate_partition` counts the readers, distinct partners and remaining gates in the same circuit. The end-to-end conditional theorem `PrivateGrid1009.eleven_of_probe_bound` has one outstanding circuit-counting hypothesis: if M=1001², K is the number of distinct partners and B is the number of other gates after excluding readers and partners, then 2M ≤ K+8B. The theorem uses the verified erased upper bound 2,023,012. An unconditional eleven-gate theorem still requires the probe-charge estimate for actual circuits. The grid input indexing here represents the active incidence geometry; it does not include an embedding into the project's full projective-plane indexing.

## Setup and previously established inputs

Let M=1001^2. Delete one horizontal line. By relabelling rows and columns and interchanging directions the choice does not affect the marginal. Let D(k), E(k) be the minimum sizes before/after deletion when k crossings of that row are free and the others are fixed off. E(k)=E(0)+k by private twins; D(0)=E(0)+10 by the eight-private-points bound and the nine-input row construction. Each crossing is essential, so each increment of D is at least one. Hence the marginal is at least ten; equality requires every increment to be one, in any ordering. See [the row restoration proof](grid-1001-marginal.md).

Suppose equality. Choosing any crossing last gives the rigid-reader property in every minimum circuit: the raw crossing is read exactly once, by an OR with another wire. Two readers, or an AND reader and its live successor, would save two gates on pinning it off. Work with one private point per line by deleting seven redundant twins on each of 2002 lines. Each such pin saves exactly one by the reverse one-OR construction. Crossing readers persist under these pins; equivalently expand an optimum of the compressed function with private OR trees to an optimum of the uncompressed one and apply rigidity there. The post-deletion row upper bound before compression is 2023010; equality at ten therefore gives a compressed pre-deletion budget of 2023010+10-7*2002=2009006.

Write R_i=x_i OR T_i for the M distinct crossing readers, K for the number of distinct partner wires, B for all other gates. Each partner rejects every raw singleton: if a selector singleton activates it then activate all lines and toggle its crossing; for a different point singleton add an endpoint of its crossing missing that point and toggle the crossing. The partner is independent of its own crossing. Thus no partner is a raw input or a reader, and M+K+B <= 2009006. The [first-consumer argument](grid-first-consumer.md) gives 2M <= K+4B (even K+5B suffices here), and an injection from the M readers to direct consumers. No consumer is a crossing reader. Briefly, a reader with only one consumer cannot share that consumer with another reader: a second reader blocks an AND on an endpoint probe, and its value can mask an OR on a nonincident pair before turning on the first crossing. Readers of degree one have exclusive neighbours; the others have at least two neighbours and each consumer takes at most two reader inputs. Hall's condition follows.

## The extra saving when a matched consumer is a partner

Fix one such matching ONCE, before choosing the cut. Exactly H of its distinct consumers are partners, where H+B >= M. Every one of these partners is an AND: an OR directly consuming R_i would accept x_i alone. Choose d columns, turn off their affine points and the vertical hub. A group consists of all readers with a common partner. A group is touched when one of its crossings is in the cut.

On this restriction any touched partner is sound (implies the incidence function). If it were true on a negative input, turn on a selected dark column in its group, still a negative input. Turn on its crossing on that column in the original circuit: the sole reader already outputs true, while an incidence now exists. This is impossible. Bypass all readers of touched groups by their raw bits and restore the restricted output by OR-ing in the modified touched partner taps. Soundness and monotonicity prevent false positives. For a lost positive the first changed reader had a still-true partner, so the repair accepts it. This remains valid when a partner depends on other groups' readers.

For every dark crossing, the matched consumer is now fed zero and folds to a constant or an alias. All 1001d such gate deletions are distinct. Let Z be the subset of their partners that are matched to a dark crossing (i.e. the matched consumer is itself the partner wire). Every member of Z becomes identically false in the modified circuit because it is AND. There is one **additional** unit of saving per member, in two disjoint cases:

* For a touched group with partner in Z the output repair can omit its tap: this saves one added OR.
* For an untouched group with partner in Z, take one of its readers. Its OR now equals its raw crossing, so remove that gate. Its group was not bypassed and it is not one of the matched consumers. Distinct partners give different readers.

These counts do not require the partner and its matched source crossing to lie in the same group. Zero propagation is applied to the already bypassed DAG. Removing further constant or alias gates preserves every modified tap and cannot invalidate the repair. Restoring the unrestricted grid by private-input substitution and appending the dark line terms costs 2004d+1001 gates. This gives the pointwise inequality from minimality
```
sum over touched groups (g-1) + |Z| <= 1003d + 1001.
```
Here g is the group size. The type of savings matters: the removal of the matched AND itself was already counted; the new credit is the omitted output OR or a different reader. For a uniform d-column cut, each of the H predetermined matched crossings is dark with probability d/1001. Hence E|Z|=dH/1001, regardless of correlation with touched groups. The same argument applies to row cuts.

## Requested case: 500 pairs and one singleton per row

Here K=501501, B<=505504 and H>=496497. A uniformly chosen three-column cut hits any same-row pair with probability 6/1001-6/(1001*1000), because its columns are distinct. The 500500 pairs contribute exactly 2997 in expectation and the singletons contribute zero. Including the extra credit gives at least 2997+3*496497/1001, strictly above the budget 4010. For example the scaled inequality would require 2997*1001+3*496497 <= 4010*1001, which fails by 475478. Pairings need not be aligned between rows. This contradiction directly excludes ten in the proposed architecture.

## Arbitrary partner groups in the same grid

Use a uniform 24-column cut and, separately, a uniform 24-row cut. Put p=24/1001. A group of size g>=2 touches at least one row and one column, and touches at least two lines in one of these orientations. Its row-hit and column-hit probabilities sum to at least p+(2p-p*23/1000)=2.977p. Groups of size one have g-1=0. Since sum(g-1)=M-K, adding the two expectation inequalities gives
```
(24/1001) * ((2977/1000)*(M-K) + 2H) <= 2*25073.
```
Substituting H >= M-B >= K-5004 gives K>=902194. Already the weaker first-probe inequality 2M<=K+5B gives K<=757755. Thus equality at ten is impossible even with arbitrary partners. The independent older 47-line rectangle certificate plus the new credit also gives K>=611406, above the stronger first-probe ceiling 508506. Neither calculation entails a general theorem for other line arrangements.

Returning to the original function, every row deletion therefore saves at least eleven gates; by symmetry so does every column deletion. Since E grows by exactly one at every crossing restoration, at least one of the 1001 increments of D is at least two. This is an existence statement and does not locate a particular k.
