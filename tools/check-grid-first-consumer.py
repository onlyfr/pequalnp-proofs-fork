"""Check first-consumer probe charges on a small AND/OR grid DAG."""
from collections import Counter
from itertools import product


def check(rows, cols, shared=False):
    points = list(product(range(rows), range(cols)))
    lines = list(range(rows + cols))
    probes = [(p, l) for p in [None, *points] for l in lines]
    # Each bit position is one probe: one selector, with at most one crossing.
    values = []
    operands = {}
    def wire(predicate):
        w = len(values)
        values.append(sum(1 << k for k, (p, l) in enumerate(probes) if predicate(p, l)))
        return w
    def gate(op, a, b):
        w = len(values)
        values.append(values[a] & values[b] if op == "and" else values[a] | values[b])
        operands[w] = (a,b)
        return w

    xs = {p: wire(lambda pt, l: pt == p) for p in points}
    ys = {i: wire(lambda p, l: i == l) for i in lines}
    # Two hub bits are off on all these probes. Seed with a valid hub-line edge.
    hub = wire(lambda p, l: False)
    carry = gate("and", hub, ys[0])
    readers, partners, terms = {}, set(), []
    for i, j in points:
        partners.add(carry)
        reader = gate("or", xs[i,j], carry)
        readers[i,j] = reader
        if not shared:
            both = gate("or", ys[i], ys[rows+j])
            carry = gate("and", reader, both)
            terms.append(carry)
    if shared:
        for l in lines:
            attached = [readers[i,j] for i,j in points if l in (i,rows+j)]
            aggregate = attached[0]
            for reader in attached[1:]:
                aggregate = gate("or", aggregate, reader)
            terms.append(gate("and", aggregate, ys[l]))
    out = terms[0]
    for t in terms[1:]:
        out = gate("or", out, t)

    outside = set(operands) - partners - set(readers.values())
    direct = {w for w in outside if set(operands[w]) & set(readers.values())}
    charges = Counter()
    for p,l in probes:
        k = probes.index((p,l))
        expected = p is not None and l in (p[0], rows+p[1])
        assert ((values[out] >> k) & 1) == expected
        if not expected:
            continue
        base = probes.index((None,l))
        r = readers[p]
        changed = next(w for w in operands if w > r and ((values[w] >> k) ^ (values[w] >> base)) & 1)
        assert r in operands[changed]
        charges[changed] += 1

    def signature(w):
        return frozenset(l for l in lines if (values[w] >> probes.index((None,l))) & 1)
    exceptional = {w for w in partners if charges[w] == 2}
    origins = set()
    for w in exceptional:
        other, = (a for a in operands[w] if a not in readers.values())
        sig = signature(other)
        assert len(sig) == 2
        origin = next(a for a in range(other+1) if signature(a) == sig)
        assert origin in outside - direct
        origins.add(origin)
    assert len(origins) == len(exceptional)
    assert all(charges[w] <= (2 if w in partners else 4) for w in charges)
    assert sum(charges.values()) == 2*len(points)
    assert 2*len(points) <= len(partners)+4*len(outside)
    assert 2*len(points) <= len(partners)+3*len(outside)
    # Check Hall directly for the two-by-two DAGs, including shared consumers.
    if len(points) == 4:
        for subset_bits in product((False, True), repeat=len(points)):
            selected = {readers[p] for p, on in zip(points, subset_bits) if on}
            neighbours = {w for w, ins in operands.items() if selected.intersection(ins)}
            assert len(neighbours) >= len(selected)
    return len(points), len(exceptional), sum(charges.values())


if __name__ == "__main__":
    for shape in ((2,2),(3,4),(5,5)):
        print(shape, "chain", check(*shape), "shared", check(*shape, shared=True))
