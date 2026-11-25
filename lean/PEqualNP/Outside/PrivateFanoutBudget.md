# A fan-out bound for the full order-1009 arc

Consider a single-output monotone circuit with binary AND and OR gates and two groups of essential inputs: N point bits and m line bits. Suppose the all-zero point assignment and the N assignments with just one point set to one induce N+1 different functions of the line bits. If the circuit has s gates, then

    N ≤ 4m + 9r + 1,       r = s - (N + m - 1).

The following is a mathematical proof. The companion Lean file checks the unary-interface bound, the skeleton count, summation and arithmetic. It does not yet construct the decomposition of a project circuit in Lean.

## Cut the circuit into trees

Fix any unused inputs to zero, propagate constants and unary gates, and discard vertices outside the output cone. This only decreases size. In the resulting DAG every essential input occurs, every gate has two incoming wires, and every vertex except the output has at least one outgoing wire. Wires are counted with multiplicity. With s now denoting the normalized size, the sum of outdegree minus one over the nonoutput vertices is 2s - (N+m+s-1) = r.

Cut **all** outgoing wires at each vertex of outdegree at least two, inserting a placeholder leaf at the receiving end of each cut wire. Retain the source vertex as the output of its own component. This includes branching input vertices. If B is the number of branching vertices then B ≤ r, and the number of cuts is B+r ≤ 2r. Every resulting component is a binary formula tree: every nonroot has a unique outgoing edge, paths terminate, and the possible roots are exactly the B cut sources and the original output. Each original input occurs in exactly one tree. Mark as ports the m original line inputs and the placeholder leaves, so there are at most m+2r ports in total.

## Count distinguishable point probes within a tree

A portless component conveys one bit. Under a singleton probe at any of its point leaves, its bit must differ from its all-off value for some line setting. Its bit here is independent of the lines, so at most one point in the component can give a distinct, nonbaseline global response.

For a tree with b ≥ 1 ports, keep the paths from its ports to its root. The pruned skeleton has b leaves, b-1 binary forks and possibly unary nodes. Assign each unary node to the closest port or fork below it, following its unique skeleton child until encountering one. This gives at most 2b-1 chains, including the chain above the top fork or sole port. Every ordinary point belongs to a hanging subtree off exactly one of these chains. Empty chains add no points.

Fix one chain. Its hanging subtrees contain only ordinary point leaves. Treat the wire from the port or fork at the bottom as an incoming bit z. The bit at the top, immediately before the next fork or at the component root, is a monotone unary function of z once the point probe is fixed. Every path from a point in those hanging subtrees to the original output passes through this top wire. Indeed the points and intervening internal vertices have unique outgoing wires until that boundary; cut sources could only be component roots. Also no point on the chain can influence z, by acyclicity and this unique exit. Consequently two probes with the same unary function produce the same global response at every line setting. This remains true if the top wire is used many times or the incoming bit depends on the line setting. With all other points off there are just three monotone unary functions: constant zero, identity and constant one. One is occupied by the all-off probe. Therefore at most two distinguishable points can be assigned to each chain.

A tree with b ports thus has at most 4b+1 ordinary points, a loose bound valid also at b=0. Summing over the trees yields N ≤ 4(m+2r)+(r+1).

## Apply to the full arc

There are 1,010 lines. Each has one private point and each unordered pair has a different shared point, so N = 1,010 + 1,010·1,009/2 = 510,555. The individual point probes induce respectively y_i and y_i OR y_j. Every pair of different supports is distinguished by setting one line in their symmetric difference. The zero-point baseline is identically false and every line input is essential. Thus s = 511,564+r and r ≥ ceil((510,555-4,040-1)/9) = 56,280, yielding **s ≥ 567,844**. At the proposed ceiling s ≤ 512,608 one would have r ≤ 1,044, allowing at most 13,437 distinguishable point probes.

The line-centered construction uses 1,021,109 gates. The point-centered construction uses 509,545 pair ORs, 510,555 point ANDs and 510,554 output ORs. The counting proof also covers interleaved, multilevel circuits. The new lower bound excludes the specific 512,608 upper-bound route. An absolute lower bound on the full set does not settle the difference of two minimum sizes after deleting a line.
