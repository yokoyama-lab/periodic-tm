#!/usr/bin/env python3
"""README の準備運動の模範解答: 開始マーカーでぴったり止まる FLIP.

rtm_sim.py の FLIP は逆実行時に初期配置を 1 歩通り過ぎた。原因は
初期状態 q0 がループ中でも再訪され、逆機械が「ここが開始点」と
分からないこと。テープ左端 (セル 0) にマーカー '>' を置き、
一度しか通らない初期状態 st から始めれば、逆機械は st に戻った
ところで規則が尽きてぴったり停止する。
"""
from rtm_sim import BLANK, Cfg, check_reversible, reverse, run

MARK = ">"

# st はマーカーを読んで mv に合流する（一度きり）。mv には q0 からの
# 書換規則も入ってくるが、書かれる記号（0/1 と '>'）が違うので後退決定的。
# 別のシフト状態 m0 を挟むと q0 に入るシフト規則が 2 本になり後退非決定に
# なる（check_reversible が正しく弾く。試してみよ）。
FLIP2 = [
    ("w", "st", MARK, MARK, "mv"),
    ("w", "q0", "0", "1", "mv"),
    ("w", "q0", "1", "0", "mv"),
    ("m", "mv", +1, "q0"),
    ("w", "q0", BLANK, BLANK, "halt"),
]


def main():
    check_reversible(FLIP2)
    inp = "0110"
    tape = {0: MARK} | {i + 1: b for i, b in enumerate(inp)}
    fwd = run(FLIP2, Cfg("st", tape))
    back = run(reverse(FLIP2), fwd[-1])
    print(f"forward : {len(fwd)} configs, halt tape = "
          f"{''.join(fwd[-1].tape.get(i, BLANK) for i in range(len(inp) + 2))}")
    print(f"backward: {len(back)} configs, final state = {back[-1].state}")
    # 今度は鏡像が「ぴったり」一致する（接頭辞比較ではなく完全一致）
    def canon(c):
        return (c.state, {i: s for i, s in c.tape.items() if s != BLANK}, c.head)
    assert [canon(c) for c in back] == [canon(c) for c in reversed(fwd)]
    print("exact mirror check: OK — 逆機械が初期配置ちょうどで停止した")


if __name__ == "__main__":
    main()
