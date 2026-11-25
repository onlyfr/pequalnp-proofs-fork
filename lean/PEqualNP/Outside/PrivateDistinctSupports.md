# Exact deletion marginal on the arc of order 1009

The minimum size with s active lines from the specified 1010-line arc is **1011s-1** for 1 ≤ s ≤ 1010. In particular, deleting a line from the full set saves exactly **1011 gates**. This is a claim for unrestricted fan-out, single-output, fan-in-at-most-two monotone Boolean circuits. The key strengthening over the previous four-gate result is to peel point inputs globally to compute the two minima separately. The peeled points need not lie on the line eventually deleted.

## Peeling pairwise distinct point supports

Let each marked point input x have a distinct, nonempty set of neighboring line bits. With all other point inputs zero, the function on that singleton probe is precisely the OR of those neighbors. For N such points any circuit needs at least 2N-1 gates (N ≥ 1).

For N ≥ 2 choose a minimal circuit, propagate constants and identities, and trim the circuit to the output. Every marked input is essential. If some point has two distinct readers, pin it to zero: both gates disappear, even if one reads the other. Otherwise each point has one reader. Consider the earliest gate that reads any point.

* If it is an AND, pin its point input to zero. The gate and at least one successor disappear. The gate cannot be the output: at least one other nonempty point support survives the restriction.
* An OR with two different point inputs would identify their singleton probes for every line assignment, since this is the sole reader of both. This contradicts distinctness, including when the two supports are strictly nested. A repeated identical operand was removed as an identity gate.
* For an OR with one point operand, the other operand depends only on line inputs. It is true when all line inputs are true. With all points initially zero, switching on the marked point then leaves this gate and the whole output unchanged, whereas the target switches from false to true.

Thus at least one zero pin saves two gates. Crucially the restricted function has the **same** line neighborhoods for all remaining points. Re-optimize and apply the same argument until one point remains. This last function needs at least one gate: it depends on the point and a line bit. This gives 2(N-1)+1. For repeated supports first keep one representative of each and pin every other point to zero, saving at least one gate per pin. If the original point count is P and there are N different nonempty supports, the lower bound is **P+N-1**. The companion Lean file formulates the marked variables on the right side of its bipartite relation, so the arc's two input blocks are interchanged. This permutation costs zero gates.

## Counts and matching construction

Write m=1010. Any s chosen arc lines have one distinct intersection for each pair, with no triple intersection. On each line exactly m-(s-1) points are private. Consequently P = choose(s,2)+s(m-s+1), whereas N = choose(s,2)+s: each pair is one support, and each line contributes one singleton support regardless of its number of private points. Then P+N-1 = s(m+1)-1.

For each active line OR its m incident point inputs using m-1 binary gates, AND the result with its line bit, and combine the s line outputs with s-1 OR gates. This attains the lower bound, so no sharing in a more general circuit can improve the minimum. The argument uses the arc incidence facts from PrivateForestLift and does not assume that the given circuit has this row structure.

For s=1010 there are 510555 different supports; both the point count and support count equal this number. Thus the full minimum is 1021109. For s=1009 the counts are P=510554 and N=509545; the minimum is 1020098. Their difference is 1011, well above ceil(1009/100)=11. All seven deletion steps from s=1004 through 1010 have the same marginal. Arbitrary active line families with points incident to three or more active lines need a separate analysis.
