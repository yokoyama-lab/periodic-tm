#!/usr/bin/env python3
"""定理 13.1（半シフト補正）の有限軌道の場合の全数検査.

research/13 の証明は「有限軌道は定理 4.1 の軌道内反射で処理」とするが、
軌道が有限かどうかは一般に判定できないので、そのままでは一様な構成に
ならない. 全軌道に ι(x) = g(f^{s}(x)), s = -ceil(τ/2) を使う素朴版は、
有限軌道で τ(C) = ℓ/2 となる場合に壊れる（最小反例 n=4:
f = (0 1)(2 3), g = (0 2 1 3) で ι は 4-サイクル）.

修正版: τ ≠ 0 かつ f^{2τ}(x) = x （判定可能）なら軌道内反射、
それ以外は g(f^{s}(x)). 無限鎖ではこの判定は成り立たないので、
鎖の側は元の証明のまま.

n 点上の全置換 f と、g f g⁻¹ = f⁻¹ かつ軌道作用が対合な全 g について、
両構成が「対合かつ f を f⁻¹ に共役する」かを検査する.
期待値（2 ≤ n ≤ 7）: 66072 組、修正版の失敗 0、素朴版の失敗 3756.
修正版に失敗があるか、素朴版に失敗が無い（＝検査が空回り）なら終了コード 1.

使い方: python3 halfshift_finite_check.py [最大 n（既定 7）]
"""
import itertools
import sys


def comp(a, b):
    return tuple(a[b[i]] for i in range(len(a)))   # a∘b


def inv(a):
    r = [0] * len(a)
    for i, x in enumerate(a):
        r[x] = i
    return tuple(r)


def pw(f, k, x):
    if k < 0:
        f, k = inv(f), -k
    for _ in range(k):
        x = f[x]
    return x


def orbit_list(f, x):
    o, y = [x], f[x]
    while y != x:
        o.append(y)
        y = f[y]
    return o


def search_t(f, g, x):
    """t = 0, 1, -1, 2, -2, ... の順に f^t(x) = g²(x) を探す."""
    gg = g[g[x]]
    for k in itertools.count():
        for t in ([0] if k == 0 else [k, -k]):
            if pw(f, t, x) == gg:
                return t


def ceil2(t):
    return -((-t) // 2)


def in_orbit_reflect(f, x):
    """定理 4.1: 基点 = 軌道の最小元 b、x = f^k(b) を f^{-k}(b) へ."""
    o = orbit_list(f, x)
    ln, b = len(o), min(o)
    k = (-o.index(b)) % ln
    return pw(f, (ln - k) % ln, b)


def iota(f, g, x, fixed):
    t = search_t(f, g, x)
    if fixed and t != 0 and pw(f, 2 * t, x) == x:
        return in_orbit_reflect(f, x)
    return g[pw(f, -ceil2(t), x)]


def is_reversing_involution(f, io):
    finv = inv(f)
    n = len(f)
    return (all(io[io[x]] == x for x in range(n))
            and all(io[f[io[x]]] == finv[x] for x in range(n)))


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    total = {"pairs": 0, False: 0, True: 0}
    first_cex = None
    for n in range(2, nmax + 1):
        perms = list(itertools.permutations(range(n)))
        cnt, bad = 0, {False: 0, True: 0}
        for f in perms:
            finv = inv(f)
            orbs = {frozenset(orbit_list(f, x)) for x in range(n)}
            for g in perms:
                if comp(comp(g, f), inv(g)) != finv:
                    continue
                # 軌道作用が対合: g² が各軌道を保つ
                if any(frozenset(orbit_list(f, g[g[min(o)]])) != o for o in orbs):
                    continue
                cnt += 1
                for fixed in (False, True):
                    io = tuple(iota(f, g, x, fixed) for x in range(n))
                    if not is_reversing_involution(f, io):
                        bad[fixed] += 1
                        if first_cex is None and not fixed:
                            first_cex = (f, g, io)
        print(f"n={n}: pairs={cnt} naive_fail={bad[False]} fixed_fail={bad[True]}")
        total["pairs"] += cnt
        total[False] += bad[False]
        total[True] += bad[True]
    print(f"total: pairs={total['pairs']} naive_fail={total[False]} "
          f"fixed_fail={total[True]}")
    print(f"first naive counterexample (f, g, iota): {first_cex}")
    ok = total[True] == 0 and total[False] > 0
    print("OK" if ok else "FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
