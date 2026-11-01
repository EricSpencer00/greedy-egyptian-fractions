"""Reproduces the tables in paper/paper.tex.

`greedy` matches the Lean definition: it works on the unreduced pair (a, b).
Run: python3 scripts/stats.py
"""
import sys
from math import gcd

sys.set_int_max_str_digits(0)


def greedy(a, b):
    out = []
    while a > 0:
        n = -(-b // a)
        out.append(n)
        a, b = a * n - b, n * b
    return out


def smallest_worst_case(a):
    """Least b > a, gcd(a, b) = 1, whose expansion has exactly a terms.

    The first step lowers the numerator by exactly 1 only when b = 1 (mod a),
    so only those b need checking.
    """
    b = a + 1
    while gcd(a, b) != 1 or len(greedy(a, b)) != a:
        b += a
    return b


def check_growth(max_b=400):
    """Checks n_{i+1} >= n_i (n_i - 1) + 1 for every reduced a/b in (0, 1) with b <= max_b."""
    for b in range(2, max_b + 1):
        for a in range(1, b):
            if gcd(a, b) != 1:
                continue
            g = greedy(a, b)
            assert all(y >= x * (x - 1) + 1 for x, y in zip(g, g[1:])), (a, b, g)


def main():
    print("Table 1: smallest b with a/b reduced and exactly a greedy terms")
    print("a  b       digits of last denominator")
    for a in range(2, 15):
        b = smallest_worst_case(a)
        print(f"{a:<2} {b:<7} {len(str(greedy(a, b)[-1]))}")
    check_growth()
    print("growth bound n_{i+1} >= n_i(n_i - 1) + 1 holds for all reduced a/b, b <= 400")
    print("4/13 ->", greedy(4, 13))
    print("5/121 last denominator has", len(str(greedy(5, 121)[-1])), "digits")


if __name__ == "__main__":
    main()
