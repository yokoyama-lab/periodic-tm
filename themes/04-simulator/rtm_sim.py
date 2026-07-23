#!/usr/bin/env python3
"""可逆 Turing 機械の最小シミュレータ（Morita 流・四つ組形式）.

規則は 2 種類:
  ("w", q, s, s2, q2)  状態 q で記号 s を読んだら s2 を書いて q2 へ
  ("m", q, d, q2)      状態 q でヘッドを d (±1) 動かして q2 へ
状態ごとに「書換規則の集まり」か「シフト規則 1 本」のどちらか
（両方は不可）。この形式なら reverse(M) が字義どおりの規則逆転で作れる。
"""
from dataclasses import dataclass, field

BLANK = "_"


@dataclass
class Cfg:
    state: str
    tape: dict = field(default_factory=dict)
    head: int = 0

    def read(self):
        return self.tape.get(self.head, BLANK)

    def show(self, lo, hi):
        cells = "".join(self.tape.get(i, BLANK) for i in range(lo, hi + 1))
        mark = " " * (self.head - lo) + "^"
        return f"{self.state:>6} |{cells}|\n{'':>6}  {mark}"


def check_reversible(rules):
    """前進・後退の両決定性を検査する（構文チェック）."""
    fwd, bwd = set(), set()
    for r in rules:
        if r[0] == "w":
            _, q, s, s2, q2 = r
            assert (q, s) not in fwd, f"forward conflict at {(q, s)}"
            assert (q2, s2) not in bwd, f"backward conflict at {(q2, s2)}"
            fwd.add((q, s)), bwd.add((q2, s2))
        else:
            _, q, _, q2 = r
            assert not any(k[0] == q for k in fwd), f"state {q} mixes rules"
            assert (q2, None) not in bwd, f"backward shift conflict at {q2}"
            fwd.add((q, None)), bwd.add((q2, None))


def reverse(rules):
    """Lecerf 反転: 書換は s <-> s2 と q <-> q2、シフトは符号も反転."""
    out = []
    for r in rules:
        if r[0] == "w":
            _, q, s, s2, q2 = r
            out.append(("w", q2, s2, s, q))
        else:
            _, q, d, q2 = r
            out.append(("m", q2, -d, q))
    return out


def step(rules, c: Cfg):
    for r in rules:
        if r[0] == "w" and r[1] == c.state and r[2] == c.read():
            c2 = Cfg(r[4], dict(c.tape), c.head)
            c2.tape[c.head] = r[3]
            return c2
        if r[0] == "m" and r[1] == c.state:
            return Cfg(r[3], dict(c.tape), c.head + r[2])
    return None


def run(rules, c: Cfg, cap=1000):
    trace = [c]
    while (n := step(rules, trace[-1])) is not None and len(trace) < cap:
        trace.append(n)
    return trace


# デモ機械 FLIP: 左端から右へ走査し、0<->1 を反転して停止する可逆 TM。
FLIP = [
    ("w", "q0", "0", "1", "mv"),
    ("w", "q0", "1", "0", "mv"),
    ("m", "mv", +1, "q0"),
    ("w", "q0", BLANK, BLANK, "halt"),
]


def main():
    check_reversible(FLIP)
    inp = "0110"
    c0 = Cfg("q0", {i: b for i, b in enumerate(inp)})
    fwd = run(FLIP, c0)
    print(f"== forward: FLIP on '{inp}' ==")
    for c in fwd:
        print(c.show(0, len(inp)))
    back = run(reverse(FLIP), fwd[-1])
    print("== backward: reverse(FLIP) from the halt config ==")
    for c in back:
        print(c.show(0, len(inp)))
    # 検証: 逆実行のトレースは前進トレースの鏡像（を接頭辞に持つ）。
    # 逆機械は初期配置を知らないので 1 歩通り過ぎる。開始マーカーを
    # 足してぴったり止める改造は README の演習を参照。
    def canon(c):  # 明示的に書かれた空白と未使用セルを同一視する
        return (c.state, {i: s for i, s in c.tape.items() if s != BLANK}, c.head)

    assert [canon(c) for c in back[: len(fwd)]] == [canon(c) for c in reversed(fwd)]
    print("mirror check: OK — 逆機械が実行を逆再生し入力を復元した")


if __name__ == "__main__":
    main()
