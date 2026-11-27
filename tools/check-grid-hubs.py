"""Check the affine grid counts and the hub-on cofactor identities."""
from collections import Counter
from itertools import product

def counts(a, b, q, horizontal_hub, vertical_hub):
    # All points have distinct tags. Collect active neighbourhoods explicitly.
    signatures = Counter()
    for i in range(a):
        signatures[(i,)] += q - b
        for j in range(b):
            signatures[(i, a+j)] += 1
    for j in range(b):
        signatures[(a+j,)] += q - a
    if horizontal_hub:
        signatures[tuple(range(a))] += 1
    if vertical_hub:
        signatures[tuple(range(a,a+b))] += 1
    points = sum(signatures.values())
    lower = points + len(signatures) - 1
    upper = sum(len(k)*v for k,v in signatures.items()) + a+b-1
    return lower, upper

def check_values():
    # Two lines in each direction, one private affine bit per line.
    for vals in product((False, True), repeat=14):
        h,v = vals[:2]
        rows,cols = vals[2:4],vals[4:6]
        rp,cp = vals[6:8],vals[8:10]
        xx = vals[10:]
        def f(active):
            return (any(rows[i] and (h or rp[i] or any(xx[2*i:2*i+2])) for i in active)
                    or any(cols[j] and (v or cp[j] or xx[j] or xx[2+j]) for j in range(2)))
        full, erased = f(range(2)), f(range(1,2))
        if h:
            assert full == (erased or rows[0])
        if v:
            assert full == (any(cols) or any(rows[i] and (h or rp[i] or any(xx[2*i:2*i+2])) for i in range(2)))
            assert erased == (any(cols) or (rows[1] and (h or rp[1] or any(xx[2:]))))
check_values()
for h,v in product((False,True), repeat=2):
    before = counts(1001,1001,1009,h,v)
    after = counts(1000,1001,1009,h,v)
    print(h,v,before,after,'lower difference bound',before[0]-after[1])
