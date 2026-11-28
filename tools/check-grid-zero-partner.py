"""Verify the extra zero-partner saving and the grid contradictions."""
from fractions import Fraction
from math import ceil, comb, floor


def verify_small_dag():
    # Truth tables for all 2^14 inputs. The vertical hub, both crossings and
    # the private point of each dark column are pinned in the reference circuit.
    width = 1 << 14
    universe = (1 << width) - 1
    inputs = [sum(1 << k for k in range(width) if k & (1 << j)) for j in range(14)]
    groups = [[(0,0), (0,1)], [(1,1)], [(1,0)]]
    source = [(0,0), (1,1)]  # Matched readers of partners 1 and 2, respectively.
    cases = set()
    for dark in ({0}, {1}, {0,1}):
        h, v = inputs[0], 0
        row, col = inputs[2:4], inputs[4:6]
        u = inputs[6:8]
        w = [0 if j in dark else inputs[8+j] for j in range(2)]
        x = {(i,j): 0 if j in dark else inputs[10+2*i+j]
             for i in range(2) for j in range(2)}
        base = (row[0] & (h|u[0])) | (row[1] & (h|u[1]))
        for j in range(2):
            base |= col[j] & (v|w[j])
        target = base
        for (i,j), bit in x.items():
            target |= bit & (row[i]|col[j])
        touched = {k for k, group in enumerate(groups) if any(j in dark for _,j in group)}
        zero = {k for k, (_,j) in enumerate(source, 1) if j in dark}
        readers = {}
        taps = []
        residual = base
        for k, group in enumerate(groups):
            if k == 0:
                tag = h & row[0]
            else:
                i,j = source[k-1]
                tag = readers[i,j] & row[i]
            if k in zero:
                assert tag == 0
                cases.add("skip tap" if k in touched else "remove untouched reader")
            if k in touched and k not in zero:
                assert tag & (universe ^ target) == 0
                taps.append(tag)
            for i,j in group:
                readers[i,j] = x[i,j] if k in touched else (x[i,j] | tag)
                if k in zero and k not in touched:
                    assert readers[i,j] == x[i,j]
                residual |= readers[i,j] & (row[i]|col[j])
        for tap in taps:
            residual |= tap
        assert residual == target
        assert len(touched-zero) + len(zero) == len(touched) + len(zero-touched)
    assert cases == {"skip tap", "remove untouched reader"}

    # Independent carry example: column 1 is dark. A true horizontal
    # incidence at (0,0) was routed via the now-bypassed reader at (0,1).
    x00, y0, v0 = inputs[10], inputs[2], inputs[4]
    carry = x00 & y0
    target = x00 & (y0 | v0)
    residual = x00 & v0
    assert target & (universe ^ residual)
    assert (residual | carry) == target


def verify_bounds():
    n = 1001
    m = n*n
    hit_pair = 1-Fraction(comb(n-2,3),comb(n,3))
    budget_b = 2009006 - m - 501501
    matched = m - budget_b
    expected = 500500*hit_pair + Fraction(3*matched,n)
    assert 500500*hit_pair == 2997 and expected-4010 == Fraction(475478,n)
    hit_two = 1-Fraction(comb(n-2,24),comb(n,24))
    assert hit_two+Fraction(24,n) == Fraction(24*2977,1000*n)
    lower = ceil((2977*m-2000*5004-Fraction(2000*n*25073,24))/977)
    upper = floor(Fraction(5*(2009006-m)-2*m,4))
    assert (lower,upper) == (902194,757755)
    print(f"Paired excess: {expected-4010}; general necessary bounds: {lower} <= K <= {upper}")


if __name__ == "__main__":
    verify_small_dag()
    verify_bounds()
