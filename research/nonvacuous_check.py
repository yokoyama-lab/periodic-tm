#!/usr/bin/env python3
"""約束集合 validPerms N ℓ ℓ 0 の非空性を全数で確かめる独立オラクル。

Lean 側の `TwoPointNonvacuous.validPerms_nonempty_iff`
（非空 ⟺ 0 < ℓ ≤ N）を、Lean とは無関係に置換を全列挙して検算する。

約束（QueryGame.Valid ℓ ℓ 0 f）:
  * f ^ ℓ = 1
  * 0 の f-軌道の濃度がちょうど ℓ
"""

from itertools import permutations


def orbit(f, x):
    """f のもとでの x の軌道（集合）。"""
    seen = {x}
    y = f[x]
    while y != x:
        seen.add(y)
        y = f[y]
    return seen


def pow_is_id(f, k):
    """f ^ k = 1 か。"""
    n = len(f)
    return all(compose_pow(f, k, x) == x for x in range(n))


def compose_pow(f, k, x):
    for _ in range(k):
        x = f[x]
    return x


def promise_nonempty(N, ell):
    """Valid ℓ ℓ 0 を満たす置換が存在するか（全数）。"""
    for p in permutations(range(N)):
        if not pow_is_id(p, ell):
            continue
        if len(orbit(p, 0)) == ell:
            return True
    return False


def main():
    bad = 0
    checked = 0
    for N in range(1, 8):
        for ell in range(0, 10):
            got = promise_nonempty(N, ell)
            want = (0 < ell <= N)
            checked += 1
            if got != want:
                bad += 1
                print(f"  BAD N={N} ell={ell}: enumerated={got} formula={want}")
    print(f"checked {checked} cells (N=1..7, ell=0..9): "
          f"nonempty <-> 0 < ell <= N   BAD={bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
