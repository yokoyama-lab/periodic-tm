#!/usr/bin/env python3
"""involution compiler (prototype) — 位数有限の可逆プログラムを
2つの対合プログラムの合成にコンパイルする.

パイプライン:
  1. 入力: ミニ可逆言語のプログラム P（有限状態空間上の全単射を計算）
  2. 検査: 局所有限性（全軌道が有限）を軌道走査で確認
  3. 変換: P から対合プログラム I1, I2 を生成し、
       [[I1]] ∘ [[I1]] = id, [[I2]] ∘ [[I2]] = id, [[I1]] ∘ [[I2]] = [[P]]
     を全状態で機械検査する
  4. 出力: I1, I2 は同じミニ言語の AST（P をサブルーチン呼び出しで使う）

意味論的正当性の根拠は局所有限分解定理
（lean/FiniteOrderTM/LocallyFinite.lean, sorry ゼロ）。この実装は
その構成（軌道走査・最小元基点・反射）をプログラム変換として写経する。

理論的位置づけ（新規性サーベイ 2026-07-29 済み）:
- Nakano RC 2020 の ITM が対合プログラムの機械モデル基底
- Gajardo–Kari–Moreira JCSS 2012 は CA で F = H∘G 分解の可否を研究
  （こちらは位数有限なら常に可能・構成的・検証つき、が差分)
"""
from __future__ import annotations
from dataclasses import dataclass
from itertools import product


# ---------------------------------------------------------------- mini language
# 状態 = レジスタのタプル。プリミティブは有限状態空間上の全単射。

@dataclass(frozen=True)
class Prim:
    """プリミティブ全単射（名前と、前進・後退の意味論）."""
    name: str
    fwd: object
    bwd: object


@dataclass(frozen=True)
class Seq:
    parts: tuple


@dataclass(frozen=True)
class Call:
    """コンパイル済みプログラムのサブルーチン呼び出し（k 乗、負も可）."""
    prog: object
    power: int


@dataclass(frozen=True)
class Reflect:
    """軌道反射コンビネータ: base() で基点と位置を求め f^{e(k,l)} を適用.

    これがコンパイラの出力の核。引数 mode ∈ {"i2", "i1"} で
    反射 k ↦ (-k) mod l （i2）/ k ↦ (1-k) mod l （i1）を選ぶ。
    """
    prog: object
    mode: str


def run(prog, s):
    if isinstance(prog, Prim):
        return prog.fwd(s)
    if isinstance(prog, Seq):
        for p in prog.parts:
            s = run(p, s)
        return s
    if isinstance(prog, Call):
        f, k = prog.prog, prog.power
        for _ in range(abs(k)):
            s = run(f, s) if k > 0 else run_bwd(f, s)
        return s
    if isinstance(prog, Reflect):
        orbit = _orbit(prog.prog, s)
        base = min(range(len(orbit)), key=lambda i: orbit[i])
        k = (0 - base) % len(orbit)          # s の基点からの位置
        l = len(orbit)
        e = (-k) % l if prog.mode == "i2" else (1 - k) % l
        return orbit[(base + e) % l]
    raise TypeError(prog)


def run_bwd(prog, s):
    if isinstance(prog, Prim):
        return prog.bwd(s)
    if isinstance(prog, Seq):
        for p in reversed(prog.parts):
            s = run_bwd(p, s)
        return s
    if isinstance(prog, Call):
        return run(Call(prog.prog, -prog.power), s)
    if isinstance(prog, Reflect):        # 反射は対合なので逆 = 自分
        return run(prog, s)
    raise TypeError(prog)


def _orbit(prog, s):
    o, t = [s], run(prog, s)
    while t != s:
        o.append(t)
        t = run(prog, t)
    return o


# ---------------------------------------------------------------- the compiler

def check_locally_finite(prog, states, cap=10**6):
    """全状態の軌道が有限（= cap 以下）で閉じることを検査."""
    for s in states:
        o, t, n = s, run(prog, s), 1
        while t != o:
            t = run(prog, t)
            n += 1
            if n > cap:
                return False
    return True


def compile_involutions(prog):
    """P ↦ (I1, I2) with [[I1]]∘[[I2]] = [[P]], both involutions."""
    return Reflect(prog, "i1"), Reflect(prog, "i2")


def verify(prog, i1, i2, states):
    for s in states:
        assert run(i2, run(i2, s)) == s, ("I2 not involutive", s)
        assert run(i1, run(i1, s)) == s, ("I1 not involutive", s)
        assert run(i1, run(i2, s)) == run(prog, s), ("I1∘I2 ≠ P", s)
    return True


def show(prog):
    if isinstance(prog, Prim):
        return prog.name
    if isinstance(prog, Seq):
        return "; ".join(show(p) for p in prog.parts)
    if isinstance(prog, Call):
        return f"call^{prog.power}({show(prog.prog)})"
    if isinstance(prog, Reflect):
        return f"reflect[{prog.mode}]({show(prog.prog)})"


# ---------------------------------------------------------------- examples

def demo():
    # 例1: RGB 回転（位数3、1レジスタ）
    rot = Prim("rot_rgb", lambda s: ((s[0] + 1) % 3,),
                          lambda s: ((s[0] - 1) % 3,))
    # 例2: 混合位数6（2レジスタ: mod-2 と mod-3 の同時回転）
    mix = Prim("mix6", lambda s: ((s[0] + 1) % 2, (s[1] + 1) % 3),
                       lambda s: ((s[0] - 1) % 2, (s[1] - 1) % 3))
    # 例3: 合成プログラム（swap とインクリメントの列、位数は非自明）
    swp = Prim("swap", lambda s: (s[1], s[0], s[2]),
                       lambda s: (s[1], s[0], s[2]))
    inc = Prim("inc2", lambda s: (s[0], s[1], (s[2] + 1) % 4),
                       lambda s: (s[0], s[1], (s[2] - 1) % 4))
    comp = Seq((swp, inc, swp, inc))

    cases = [
        ("rot_rgb  (order 3)", rot, [(i,) for i in range(3)]),
        ("mix6     (order 6)", mix, list(product(range(2), range(3)))),
        ("seq-prog (composite)", comp, list(product(range(2), range(2), range(4)))),
    ]
    for name, p, states in cases:
        assert check_locally_finite(p, states)
        i1, i2 = compile_involutions(p)
        verify(p, i1, i2, states)
        print(f"{name}: OK  P = {show(p)}")
        print(f"  I1 = {show(i1)}")
        print(f"  I2 = {show(i2)}")
    print("involution compiler prototype: all checks passed")


if __name__ == "__main__":
    demo()
