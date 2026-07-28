#!/usr/bin/env python3
"""SRL バックエンド — 対合プログラムを RFCL/SRL の実コードとして出力する.

鍵となる観察: **対合 = 互いに素な互換（2サイクル）の積**。
ゆえに有限領域の対合 ι は、各互換 {a, b} を可逆な条件分岐

    if (= x a) then x += (b-a);
    else if (= x b) then x -= (b-a); else fi (= x a) fi (= x b)

の列として SRL に直訳できる（互換どうしの台が素なので順序任意・
条件の干渉なし）。出射した SRL プログラムは

  1. RFCL 自身のパーサで往復（テキスト → AST）
  2. RFCL インタプリタで全入力について ι と一致することを検査
  3. RFCL の**プログラムインバータ**で反転し、逆プログラムの意味論も
     ι に一致（= プログラムレベルの対合性）を検査

パイプライン全体: P → (I1, I2) [invcomp] → 各 Ii の互換分解
→ SRL ソースコード。ITM バックエンド（機械）と並ぶ言語側の出口。
"""
import sys
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path.home() / "dev/github.com/yokoyama-lab/RFCL"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from pyrev_fl.parser import parse_program              # noqa: E402
from pyrev_fl.interpreter import run_program           # noqa: E402
from pyrev_fl.invert import invert_program             # noqa: E402
from pyrev_fl.pretty import render_program             # noqa: E402
from invcomp import Prim, compile_involutions, run as prun   # noqa: E402


def transpositions(iota, domain):
    """対合の互換分解（対合性の検査つき）."""
    seen, pairs = set(), []
    for a in domain:
        b = iota(a)
        assert iota(b) == a, "not an involution"
        if a != b and a not in seen:
            pairs.append((min(a, b), max(a, b)))
            seen |= {a, b}
    return pairs


def emit_srl(iota, domain, var="x"):
    """対合 ι を SRL ソースコードへ（1整数レジスタ、互換のカスケード）."""
    body = []
    for a, b in transpositions(iota, domain):
        d = b - a
        body.append(
            f"if (= {var} {a}) then\n"
            f"  {var} += {d};\n"
            f"else\n"
            f"  if (= {var} {b}) then\n"
            f"    {var} -= {d};\n"
            f"  else\n"
            f"  fi (= {var} {a})\n"
            f"fi (= {var} {b})"
        )
    src = f"({var}) ({var}) ()\n" + "\n".join(body) + "\n"
    return src


def srl_semantics(program, x):
    store = run_program(program, [x])
    return store["x"] if not hasattr(store, "vars") else store.vars["x"]


def demo():
    rot = Prim("rot_rgb", lambda s: ((s[0] + 1) % 3,),
                          lambda s: ((s[0] - 1) % 3,))
    mix = Prim("mix6", lambda s: ((s[0] + 1) % 2, (s[1] + 1) % 3),
                       lambda s: ((s[0] - 1) % 2, (s[1] - 1) % 3))
    cases = [
        ("rot_rgb", rot, [(i,) for i in range(3)]),
        ("mix6", mix, list(product(range(2), range(3)))),
    ]
    for label, P, states in cases:
        enc = {s: i for i, s in enumerate(states)}   # 状態を整数に符号化
        dec = {i: s for s, i in enc.items()}
        i1, i2 = compile_involutions(P)
        for name, ip in (("I1", i1), ("I2", i2)):
            iota = lambda v, ip=ip: enc[prun(ip, dec[v])]
            dom = range(len(states))
            src = emit_srl(iota, dom)
            prog = parse_program(src)                       # 1. 往復
            for v in dom:                                   # 2. 意味論 = ι
                assert srl_semantics(prog, v) == iota(v), (label, name, v)
            inv = invert_program(prog)                      # 3. 逆 = ι
            for v in dom:
                assert srl_semantics(inv, v) == iota(v), (label, name, v)
            print(f"{label}/{name}: OK — SRL "
                  f"({len(transpositions(iota, dom))} transpositions, "
                  f"interp = iota, inverter(prog) = iota)")
        # 直列: I2 の SRL 実行 → I1 の SRL 実行 = P
        io1 = lambda v: enc[prun(i1, dec[v])]
        io2 = lambda v: enc[prun(i2, dec[v])]
        p1 = parse_program(emit_srl(io1, range(len(states))))
        p2 = parse_program(emit_srl(io2, range(len(states))))
        for s in states:
            v = srl_semantics(p1, srl_semantics(p2, enc[s]))
            assert dec[v] == prun(P, s)
        print(f"{label}: OK — SRL-level I1;I2 = P on {len(states)} states")
    # 出力例を1つ表示
    iota_show = lambda v: enc[prun(i2, dec[v])]
    print("\n--- sample emitted SRL (mix6 / I2) ---")
    print(emit_srl(iota_show, range(6)))


if __name__ == "__main__":
    demo()
