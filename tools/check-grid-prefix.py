"""Check the prefix construction on every input of the two-by-two grid."""
from itertools import product


def check():
    tested = 0
    for bits in product((False, True), repeat=14):
        h_hub, v_hub = bits[:2]
        rows, cols = bits[2:4], bits[4:6]
        row_private, col_private, crossings = bits[6:8], bits[8:10], bits[10:]
        base = any(y and (h_hub or u) for y, u in zip(rows, row_private))
        base |= any(y and (v_hub or u) for y, u in zip(cols, col_private))
        selected = any(rows) or any(cols)
        tag = h_hub and (v_hub or rows[0])
        plain = tag
        expected = base
        for k, x in enumerate(crossings):
            enabled = rows[k // 2] or cols[k % 2]
            reader = x or tag
            tag = tag or (reader and enabled)
            plain = plain or (x and enabled)
            assert tag == plain
            expected |= x and enabled
        assert (base or (tag and selected)) == expected
        # A second construction carries horizontal incidences along each row.
        carry_output = bare_output = base
        for i, y in enumerate(rows):
            enable = (y or h_hub) and (y or v_hub)
            carry = h_hub and (v_hub or y)
            for j, z in enumerate(cols):
                x = crossings[2*i+j]
                reader = x or carry
                carry_output |= reader and z
                bare_output |= x and z
                carry = reader and enable
            carry_output |= carry and y
            bare_output |= crossings[2*i+1] and enable and y
        assert carry_output == expected
        assert not bare_output or expected
        if sum(bits) == 2:
            missed = any(rows[i] and crossings[2*i] for i in range(2))
            assert (expected and not bare_output) == missed
        tested += 1
    return tested


if __name__ == "__main__":
    size = 1001**2
    print("Exhaustive two-by-two assignments:", check())
    print("Full-scale distinct partners:", size)
    print("Full-scale distinct crossing-selector labels:", 2*(size-1))
    print("Full-scale removable readers:", size)
    print("Row-carry distinct matched losses:", 1001*1000)
