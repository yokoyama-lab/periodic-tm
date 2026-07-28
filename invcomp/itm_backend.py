#!/usr/bin/env python3
"""ITM バックエンド — 対合プログラムを Nakano 型機械へコンパイルする.

パイプライン全体:
  P (位数有限の可逆プログラム)
    → invcomp: I1, I2 (対合プログラム)
    → 本ファイル: M1, M2 (書換規則の Turing 機械, themes/04 の四つ組形式)
    → 検査:
       (a) 各 Mi が「構文的に対合的」: 規則集合を Lecerf 反転した結果が、
           状態の対合的リネーム σ でちょうど元の規則集合に戻る
           (Nakano RC 2020 の ITM の構文対称性のプロトタイプ版)
       (b) 機械意味論で Mi を2回走らせると恒等 (f∘f = id)
       (c) M1 → M2 の直列実行の機械意味論が P に一致

有限領域の状態をテープ記号1マスにエンコードする最小構成
(文字列エンコード + I/O 規約への拡張は README の残作業 3)。
"""
import sys
from itertools import permutations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "themes" / "04-simulator"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from rtm_sim import Cfg, check_reversible, reverse, run          # noqa: E402
from invcomp import (Prim, Seq, compile_involutions,             # noqa: E402
                     check_locally_finite, run as prun)
from itertools import product                                    # noqa: E402


def build_write_machine(fn, states, name):
    """有限全単射 fn を「1マス書換で計算する」機械にする.

    規則: (q0, s) → (fn(s) を書いて halt)。fn が対合なら、この機械は
    構文的にも対合的になる（下の検査で確認する）。"""
    syms = {s: f"{name}:{i}" for i, s in enumerate(states)}
    rules = [("w", "q0", syms[s], syms[fn(s)], "halt") for s in states]
    check_reversible(rules)
    return rules, syms


def is_syntactically_involutory(rules):
    """∃ 状態対合 σ: rename(σ, reverse(rules)) = rules を全探索で判定."""
    states = sorted({r[1] for r in rules} | {r[-1] for r in rules})
    rev = reverse(rules)
    for perm in permutations(states):
        sigma = dict(zip(states, perm))
        if any(sigma[sigma[q]] != q for q in states):
            continue                                  # σ は対合に限る
        renamed = {(k, sigma[q], a, b, sigma[q2]) if k == "w"
                   else (k, sigma[q], d, sigma[q2])
                   for (k, q, a, b, q2) in [(r[0], r[1], *r[2:-1], r[-1])
                                            for r in rev]}
        if renamed == set(map(tuple, rules)):
            return sigma
    return None


def machine_apply(rules, sym):
    """1マス機械の意味論: 記号 sym を置いて走らせ、halt 時の記号を返す."""
    trace = run(rules, Cfg("q0", {0: sym}))
    assert trace[-1].state == "halt"
    return trace[-1].tape[0]


def demo():
    rot = Prim("rot_rgb", lambda s: ((s[0] + 1) % 3,),
                          lambda s: ((s[0] - 1) % 3,))
    mix = Prim("mix6", lambda s: ((s[0] + 1) % 2, (s[1] + 1) % 3),
                       lambda s: ((s[0] - 1) % 2, (s[1] - 1) % 3))
    cases = [
        ("rot_rgb (order 3)", rot, [(i,) for i in range(3)]),
        ("mix6    (order 6)", mix, list(product(range(2), range(3)))),
    ]
    for label, P, states in cases:
        assert check_locally_finite(P, states)
        i1, i2 = compile_involutions(P)
        f1 = lambda s, i1=i1: prun(i1, s)
        f2 = lambda s, i2=i2: prun(i2, s)
        M1, syms = build_write_machine(f1, states, "s")
        M2, _ = build_write_machine(f2, states, "s")

        # (a) 構文的対合性
        s1, s2 = is_syntactically_involutory(M1), is_syntactically_involutory(M2)
        assert s1 is not None and s2 is not None
        # (b) 機械レベルの f∘f = id
        for s in states:
            assert machine_apply(M1, machine_apply(M1, syms[s])) == syms[s]
            assert machine_apply(M2, machine_apply(M2, syms[s])) == syms[s]
        # (c) 直列合成 = P の機械意味論
        inv = {v: k for k, v in syms.items()}
        for s in states:
            got = inv[machine_apply(M1, machine_apply(M2, syms[s]))]
            assert got == prun(P, s), (label, s)
        print(f"{label}: OK — M1, M2 syntactically involutory "
              f"(σ={ {k: v for k, v in s1.items() if k != v} }), "
              f"machine-level I1∘I2 = P on {len(states)} states")
    print("ITM backend prototype: all machine-level checks passed")


if __name__ == "__main__":
    demo()
