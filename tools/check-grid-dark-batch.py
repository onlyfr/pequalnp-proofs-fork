"""Check simultaneous dark-column restoration and the integer lower bound."""
from fractions import Fraction
from itertools import product
from math import ceil, comb


def check_restoration():
    for bits in product((False, True), repeat=14):
        h, v = bits[:2]
        rows, cols = bits[2:4], bits[4:6]
        u, w, x = bits[6:8], bits[8:10], bits[10:]
        full = any(rows[i] and (u[i] or h or any(x[2*i:2*i+2])) for i in range(2))
        full |= any(cols[j] and (w[j] or v or x[j] or x[2+j]) for j in range(2))
        for dark in ((0,), (1,), (0, 1)):
            lit = set(range(2)).difference(dark)
            new_u = [u[i] or any(x[2*i+j] for j in dark) for i in range(2)]
            restricted = any(rows[i] and (new_u[i] or h or any(x[2*i+j] for j in lit))
                             for i in range(2))
            restricted |= any(cols[j] and (w[j] or v or x[j] or x[2+j]) for j in lit)
            restored = restricted or any(cols[j] and (w[j] or v or x[j] or x[2+j]) for j in dark)
            assert restored == full


def score(c):
    t = min(c, 7)
    return 2000*t - 23*t*(t-1)


def check_bound():
    n, d = 1001, 24
    for c in range(1, n+1):
        hit = 1 - Fraction(comb(n-c, d), comb(n, d))
        assert hit >= Fraction(d*score(c), 2000*n)
    for r, c in product(range(1, 8), repeat=2):
        for g in range(1, r*c+1):
            assert 12678*g <= 26988 + (g-1)*(score(r)+score(c))
    budget = n*d + (n-d) + (n+3)*d
    lower = ceil((12678*n*n - Fraction(2*2000*n*budget, d))/26988)
    assert lower == 167199
    print(f"Restoration gates: {budget}; partner lower bound: {lower}")


if __name__ == "__main__":
    check_restoration()
    check_bound()
