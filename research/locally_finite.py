#!/usr/bin/env python3
"""定理 4.1（局所有限分解定理）の実験検証.

一様な位数上界を持たない（軌道長が非有界な）計算可能全単射でも、
軌道走査だけで f = i1 . i2 に分解できることを確認する。
finite_order.decompose と違い、大域的な位数 n を一切使わない。

対象 f: ブロック k = 1, 2, 3, ... ごとに長さ k の巡回（軌道長が
1, 2, 3, ... と非有界に伸びる）。おまけで D∞ 例（x+1 = 2対合の積、
無限位数）も関数レベルで検査する。
"""


def f_unbounded(x: int) -> int:
    """ブロック k（開始位置 k(k-1)/2）内で +1 mod k する巡回。"""
    k, start = 1, 0
    while x >= start + k:
        start += k
        k += 1
    return start + (x - start + 1) % k


def orbit(f, x):
    """x の軌道を x に戻るまで走査（停止性は軌道の有限性から）。"""
    o = [x]
    y = f(x)
    while y != x:
        o.append(y)
        y = f(y)
    return o


def decompose_locally_finite(f):
    """位数の知識なしの二対合分解（定理 4.1 の構成そのまま）。"""
    def canonical(x):
        o = orbit(f, x)
        b = min(o)                       # 正準基点 = 軌道の最小元
        o = o[o.index(b):] + o[:o.index(b)]
        return o, o.index(x)

    def i2(x):
        o, k = canonical(x)
        return o[(-k) % len(o)]

    def i1(x):
        o, k = canonical(x)
        return o[(1 - k) % len(o)]

    return i1, i2


def main():
    i1, i2 = decompose_locally_finite(f_unbounded)
    N = 500                              # 軌道長 ~31 まで、位数の一様上界なし
    for x in range(N):
        assert i2(i2(x)) == x and i1(i1(x)) == x, f"involution fails at {x}"
        assert i1(i2(x)) == f_unbounded(x), f"composition fails at {x}"
    print(f"Theorem 4.1 check: OK on 0..{N-1} "
          f"(orbit lengths up to {len(orbit(f_unbounded, N-1))}, no uniform bound used)")

    # D-infinity: 無限位数でも 2 対合の積になる例（命題 4.2）
    s, t = (lambda x: -x), (lambda x: 1 - x)
    for x in range(-200, 200):
        assert s(s(x)) == x and t(t(x)) == x and t(s(x)) == x + 1
    print("Prop 4.2 check: OK — x+1 = (1-x) . (-x) on -200..199")


if __name__ == "__main__":
    main()
