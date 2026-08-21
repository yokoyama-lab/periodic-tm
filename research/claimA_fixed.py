#!/usr/bin/env python3
"""主張A（補題9.7）の **修正版** 判定条件とその全数検査.

背景
----
`claimA_check.py` が検査している紙の式

    ∃ m | ℓ:  max(k1+1, q+r+2-ℓ) ≤ m ≤ N-ℓ                      … (旧式)

は下界領域 q < min(ℓ-2, k1*) では brute と一致するが、**領域外では 8 件
外れる**（すべて式 = True・真 = False、つまり過大評価）。原因は
`q+r+2-ℓ` という「頂点の総数勘定」が**迷いパスのアトミック性**
（j 辺の迷いパスは j+1 頂点の塊で、1 つのサイクルに丸ごと入るしかない）を
無視していることにある。

修正版
------
別軌道完成が存在する ⟺ ある m と迷いパスの割り当てが存在して

  * m | ℓ,  k1+1 ≤ m ≤ N-ℓ                     （1 の軌道長）
  * 迷いパス（サイズ s_i = j_i+1 の塊）を S0 ⊎ S1 ⊎ Rest に分割し
      - sum(S0) ≤ ℓ - (k0+1)                   （0 の軌道の空き）
      - sum(S1) ≤ m - (k1+1)                   （1 の軌道の空き）
      - Rest は各群の合計が ℓ の約数 d 以下になるように群分けできる
  * 空き（各サイクルの詰め物）の総数 ≤ U = N - (q+r+2)（未開示点の数）

1 | ℓ なので余った未開示点は不動点にできる。よって上の条件だけでよい。

旧式との関係: **どちらの含意も成り立たない**（2026-08-22 に確定）。

  * 旧式 ⇒ 修正版 は破れる — 既知の 8 件（N ≤ 10）。旧式の**過大評価**。
  * 修正版 ⇒ 旧式 も破れる — `N=11, ℓ=6, k0=k1=0, strays=[1,1,1,1]`。
    旧式の**過小評価**。`q+r+2-ℓ ≤ m` は「0 の軌道の外の開示頂点は
    すべて 1 の軌道に入る」と決めつけているが、開示頂点は**第三の
    サイクル**に入ってよい。この状態の実際の完成は
    `(0 2 3 4 5 10)(1)(6 7)(8 9)` で、1 の軌道長は m = 1 しかない。
    N ≤ 10 で誰も見つけていなかったため、前夜までの記録は
    「式は過大評価する側にのみ外れる」と書いていた。これは誤り。

過小評価の側は下界の証明を壊しうる向きなので重要だが、この状態は
q = 4 > min(ℓ-2, k1*(11,6)) = 3 で**領域外**であり、定理9.6 は無傷。

使い方:
    python3 claimA_fixed.py             # 既定範囲（claimA_check.py と同じ）
    python3 claimA_fixed.py --wide      # ℓ=7 と N=11 まで広げる（遅い）
    python3 claimA_fixed.py --cross     # fixed と fixed_greedy の突き合わせのみ
                                         # （brute を使わないので ℓ=8, N=14 まで速い）
"""
import itertools
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from query_lb_search import Timeout, completions, orbit_of  # noqa: E402


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def _pack_rest(sizes, u, l):
    """残りの塊 sizes を、ℓ の約数長のサイクルに詰められるか.

    各群の合計 ≤ d（d | ℓ）で、詰め物の合計が未開示点 u 以内。
    余った未開示点は不動点（長さ1、1 | ℓ）になるので気にしない。"""
    if not sizes:
        return True
    s0, rest = sizes[0], sizes[1:]
    m = len(rest)
    for mask in range(1 << m):
        tot = s0 + sum(rest[i] for i in range(m) if mask >> i & 1)
        for d in divisors(l):
            pad = d - tot
            if 0 <= pad <= u:
                rem = tuple(rest[i] for i in range(m) if not mask >> i & 1)
                if _pack_rest(rem, u - pad, l):
                    return True
    return False


def fixed(N, l, k0, k1, strays):
    """修正版の判定（別軌道完成が存在するか）."""
    q = k0 + k1 + sum(strays)
    r = len(strays)
    used = q + r + 2                       # 開示済み頂点の総数
    if used > N:
        return None                        # 状態が N に入らない
    U = N - used                           # 未開示点
    blocks = [j + 1 for j in strays]       # 迷いパスの頂点数（塊）
    n = len(blocks)
    cap0 = l - (k0 + 1)                    # 0 の軌道の空き
    for m in divisors(l):
        if m < k1 + 1 or m > N - l:
            continue
        cap1 = m - (k1 + 1)                # 1 の軌道の空き
        # 塊を S0 / S1 / Rest に三分割して全探索（この範囲では n ≤ 4）
        for assign in range(3 ** n):
            a, s0, s1, rest = assign, 0, 0, []
            for i in range(n):
                which = a % 3
                a //= 3
                if which == 0:
                    s0 += blocks[i]
                elif which == 1:
                    s1 += blocks[i]
                else:
                    rest.append(blocks[i])
            if s0 > cap0 or s1 > cap1:
                continue
            pad = (cap0 - s0) + (cap1 - s1)   # 2 つの軌道に要る詰め物
            if pad > U:
                continue
            if _pack_rest(tuple(sorted(rest, reverse=True)), U - pad, l):
                return True
    return False


def old_formula(N, l, k0, k1, strays):
    """紙の式（claimA_check.formula と同一。ここでは比較用に再掲）."""
    q = k0 + k1 + sum(strays)
    r = len(strays)
    lo = max(k1 + 1, q + r + 2 - l)
    return any(lo <= m <= N - l for m in divisors(l))


def fixed_greedy(N, l, k0, k1, strays):
    """`fixed` と**独立に書いた**別実装（同じ判定条件の別アルゴリズム）.

    `_pack_rest` の再帰的な部分集合探索の代わりに、迷いパスの塊を
    「orbit(0) / orbit(1) / 第三サイクル 2..r+1（各サイクルは相異なる）」
    の r+2 通りのラベルへ総当たりで割り当て、各第三サイクルはラベル内の
    合計を包む ℓ の**最小**約数 1 つのサイクルに詰めると仮定して判定する
    （`_pack_rest` は複数の塊を同じサイクルにまとめる自由度と、複数の
    候補約数を試す自由度を両方持つ点で異なる。ここではラベル自体が
    「どの塊をどのサイクルにまとめるか」を表現し、詰める約数は最小の
    ものに固定する——ラベル分割を全数化すれば最小約数を選ぶだけで
    最適性が保てるという別の議論に基づく）。"""
    blocks = [j + 1 for j in strays]
    r = len(blocks)
    q = k0 + k1 + sum(strays)
    used = q + r + 2
    if used > N:
        return None                        # 状態が N に入らない
    U = N - used
    if k0 + 1 > l:
        return False
    for m in divisors(l):
        if not (k1 + 1 <= m <= N - l):
            continue
        for labeling in itertools.product(range(r + 2), repeat=r):
            s0 = sum(blocks[i] for i in range(r) if labeling[i] == 0)
            s1 = sum(blocks[i] for i in range(r) if labeling[i] == 1)
            if s0 > l - (k0 + 1) or s1 > m - (k1 + 1):
                continue
            pad = (l - (k0 + 1) - s0) + (m - (k1 + 1) - s1)
            ok = True
            for c in range(2, r + 2):
                t = sum(blocks[i] for i in range(r) if labeling[i] == c)
                if t == 0:
                    continue
                cands = [d for d in divisors(l) if d >= t]
                if not cands:
                    ok = False
                    break
                pad += min(cands) - t
            if ok and pad <= U:
                return True
    return False


def cross_check(wide=False):
    """`fixed` と `fixed_greedy`（独立実装）の全数突き合わせ（brute 不使用）.

    main と同じ入れ子（l → N → k0 → k1 → stray_partitions）を掃引するが、
    高価な brute は呼ばない分、既定より広い範囲を高速に検査できる。"""
    ls = (3, 4, 5, 6, 7, 8) if wide else (3, 4, 5, 6)
    nmax = 14 if wide else 11
    checked = 0
    disagreements = []
    for l in ls:
        for N in range(l + 1, nmax):
            for k0 in range(0, l - 1):
                for k1 in range(0, l - 1 - k0):
                    for strays in stray_partitions(l - 2 - k0 - k1):
                        st = list(strays)
                        fx = fixed(N, l, k0, k1, st)
                        fg = fixed_greedy(N, l, k0, k1, st)
                        if fx is None and fg is None:
                            continue        # 状態が N に入らない（両者一致）
                        checked += 1
                        if fx != fg:
                            disagreements.append((N, l, k0, k1, st, fx, fg))
    for (N, l, k0, k1, st, fx, fg) in disagreements:
        print(f"CROSS MISMATCH N={N} l={l} k0={k0} k1={k1} strays={st} "
              f"fixed={fx} fixed_greedy={fg}")
    print(f"cross-check: {checked} states, disagreements={len(disagreements)}")
    assert len(disagreements) == 0
    return disagreements


def brute(N, l, k0, k1, strays, cap=120):
    """全完成を列挙して別軌道完成の存在を全数判定（claimA_check と同じ）."""
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
        s = nxt
        nxt += 1
        path(s, js)
    if nxt > N:
        return None
    deadline = time.monotonic() + cap
    try:
        for f in completions(dict(T), N, l, l, deadline):
            if 1 not in orbit_of(f, 0):
                return True
    except Timeout:
        return "t/o"      # 打ち切り。検査せず数えるだけ（黙って飛ばさない）
    return False


def stray_partitions(budget):
    def gen(rest, mx):
        yield ()
        for first in range(1, min(rest, mx) + 1):
            for tail in gen(rest - first, first):
                yield (first,) + tail
    return gen(budget, budget)


def k1star(N, l):
    for k in range(0, l):
        cand = [d for d in divisors(l) if d >= k + 1]
        if cand and min(cand) > N - l:
            return k
    return l - 2


def main():
    if "--cross" in sys.argv[1:]:
        cross_check(wide=True)
        return
    wide = "--wide" in sys.argv[1:]
    ls = (3, 4, 5, 6, 7) if wide else (3, 4, 5, 6)
    nmax = 12 if wide else 11
    checked = bad = timedout = 0
    old_diff = []          # 修正版と旧式が食い違った状態
    under = 0              # 旧式の過小評価（真は存在するのに旧式が False）
    over = 0               # 旧式の過大評価（旧式が True なのに真は不存在）
    region_checked = 0
    for l in ls:
        for N in range(l + 1, nmax):
            v = min(l - 2, k1star(N, l))
            for k0 in range(0, l - 1):
                for k1 in range(0, l - 1 - k0):
                    for strays in stray_partitions(l - 2 - k0 - k1):
                        st = list(strays)
                        b = brute(N, l, k0, k1, st)
                        if b is None:
                            continue
                        if b == "t/o":
                            timedout += 1
                            continue
                        fx = fixed(N, l, k0, k1, st)
                        od = old_formula(N, l, k0, k1, st)
                        checked += 1
                        q = k0 + k1 + sum(st)
                        if q < v:
                            region_checked += 1
                        if fx != b:
                            bad += 1
                            print(f"FIXED MISMATCH N={N} l={l} k0={k0} "
                                  f"k1={k1} strays={strays} brute={b} "
                                  f"fixed={fx}")
                        if b and not od:
                            under += 1
                            print(f"OLD-FORMULA UNDERCOUNTS N={N} l={l} "
                                  f"k0={k0} k1={k1} strays={strays} "
                                  f"(brute=True, old=False)")
                        if od and not b:
                            over += 1
                        if fx != od:
                            old_diff.append((N, l, k0, k1, st, b, od))
    print("-- states where the corrected criterion differs from the old "
          "formula --")
    for (N, l, k0, k1, st, b, od) in old_diff:
        print(f"N={N} l={l} k0={k0} k1={k1} strays={st} "
              f"brute={b} old={od} fixed={not od}")
    print(f"checked {checked} states ({region_checked} inside the "
          f"lower-bound region): corrected-vs-brute BAD={bad}; "
          f"old-formula over-counts={over} under-counts={under} "
          f"(all {len(old_diff)} repaired by the corrected criterion); "
          f"brute timed out (unchecked)={timedout}")
    # 修正版が brute と食い違うことだけが「あってはならない」こと。
    # 旧式が両方向に外れるのは既知の事実（docstring 参照）なので数えるだけ。
    assert bad == 0


if __name__ == "__main__":
    main()
