#!/usr/bin/env python3
"""主張A（補題9.7）の二重実装照合 — exact-rev-complexity 方式.

主張A: 新鮮応答状態（P0: k0辺, P1: k1辺, 迷いパス sizes）で
別軌道完成が存在する ⟺ ∃ m | ℓ: max(k1+1, q+r+2-ℓ) ≤ m ≤ N-ℓ.

独立実装1: この式（紙の証明で導いた区間・約数条件）。
独立実装2: query_lb_search.completions による全完成の брute force
（f^ℓ=id・0の軌道長ℓの全完成を列挙し、1 が 0 の軌道外のものを探す）。

全状態（N ≤ 10, ℓ ∈ {3,4,5,6}, q ≤ ℓ-2 の新鮮応答状態の同型類）で
両者の一致を検査する。
"""
import sys, time
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from query_lb_search import completions, orbit_of


def formula(N, l, k0, k1, strays):
    q = k0 + k1 + sum(strays)
    r = len(strays)
    lo = max(k1 + 1, q + r + 2 - l)
    return any(lo <= m <= N - l for m in range(1, l + 1) if l % m == 0)


def brute(N, l, k0, k1, strays):
    """状態を具体的な部分関数 T に組み、別軌道完成の存在を全数判定."""
    T, nxt = {}, 2
    def path(start, edges):
        nonlocal nxt
        cur = start
        for _ in range(edges):
            T[cur] = nxt
            cur = nxt
            nxt += 1
        return cur
    path(0, k0)
    path(1, k1)
    for js in strays:
        s = nxt; nxt += 1
        path(s, js)
    if nxt > N:
        return None                    # 状態が N に入らない
    deadline = time.monotonic() + 120
    for f in completions(dict(T), N, l, l, deadline):
        if 1 not in orbit_of(f, 0):
            return True
    return False


def stray_partitions(budget):
    """迷いパスの辺数の多重集合（各 ≥ 1）を列挙."""
    def gen(rest, mx):
        yield ()
        for first in range(1, min(rest, mx) + 1):
            for tail in gen(rest - first, first):
                yield (first,) + tail
    return gen(budget, budget)


def k1star(N, l):
    for k in range(0, l):
        cand = [d for d in range(1, l + 1) if l % d == 0 and d >= k + 1]
        if cand and min(cand) > N - l:
            return k
    return l - 2  # 実効的に ∞（値は l-2 で頭打ち）


def main():
    """検査は2層。

    (A) 下界領域 q < min(ℓ-2, k1*)：式と brute が一致し、かつ両方
        「実行可能」であること（定理9.6の下界が実際に使う主張）。
        ここでの不一致は定理の反例なので assert で落とす。
    (B) 領域外：不一致を記録として出力する（既知: 式の(⇐)は迷いパスの
        アトミック性を無視しており、未開示点枯渇時に過大評価する）。
    """
    in_ok = in_bad = out_mis = checked = 0
    for l in (3, 4, 5, 6):
        for N in range(l + 1, 11):
            v = min(l - 2, k1star(N, l))
            for k0 in range(0, l - 1):
                for k1 in range(0, l - 1 - k0):
                    for strays in stray_partitions(l - 2 - k0 - k1):
                        st = list(strays)
                        b = brute(N, l, k0, k1, st)
                        if b is None:
                            continue
                        fm = formula(N, l, k0, k1, st)
                        checked += 1
                        q = k0 + k1 + sum(st)
                        if q < v:
                            if b == fm and b:
                                in_ok += 1
                            else:
                                in_bad += 1
                                print(f"REGION MISMATCH N={N} l={l} k0={k0} "
                                      f"k1={k1} strays={strays} b={b} fm={fm}")
                        elif b != fm:
                            out_mis += 1
    print(f"checked {checked} states: lower-bound region OK={in_ok} "
          f"BAD={in_bad}; outside-region known mismatches={out_mis}")
    assert in_bad == 0


if __name__ == "__main__":
    main()
