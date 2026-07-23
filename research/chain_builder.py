#!/usr/bin/env python3
"""Phase 1–2 の構成基盤: 鎖片の段階的連結による計算可能全単射の構成.

05-infinite-orbits-plan.md の実装。3つを機械検査する。

1. 全域性の期限管理 — 段階 s までに番地 < s の f 値と f^{-1} 値を確定
   させる規約で、極限の f が全単射になること（Phase 2 の技術的問題1）。
2. 実現補題 — c.e. 集合 S を軌道所属問題に埋め込めること（Phase 1）。
3. 単一要件の撃破 — 反転対称性の候補 ι が有限スナップショットに基づいて
   値を確約すると、敵対者が鎖の連結でその確約を偽にできること（Phase 2）。
"""
from __future__ import annotations


class ChainBuilder:
    """f を有限鎖片の集まりとして段階的に構成する。

    不変条件: f は部分単射で、各連結成分は有限パス（両端が開いている）。
    一度定義した f の値は変更しない（f の計算可能性の根拠）。
    """

    def __init__(self):
        self.succ: dict[int, int] = {}
        self.pred: dict[int, int] = {}
        self.next_fresh = 0

    def fresh(self) -> int:
        n = self.next_fresh
        self.next_fresh += 1
        return n

    def new_chain(self, length: int = 1) -> list[int]:
        nodes = [self.fresh() for _ in range(length)]
        for a, b in zip(nodes, nodes[1:]):
            self._set(a, b)
        return nodes

    def _set(self, a: int, b: int):
        assert a not in self.succ and b not in self.pred, "would break injectivity"
        self.succ[a] = b
        self.pred[b] = a

    def head(self, x: int) -> int:
        while x in self.pred:
            x = self.pred[x]
        return x

    def tail(self, x: int) -> int:
        while x in self.succ:
            x = self.succ[x]
        return x

    def link(self, a: int, b: int):
        """a の鎖の末尾を b の鎖の先頭に接続する（別鎖であること）。"""
        ta, hb = self.tail(a), self.head(b)
        assert self.head(a) != hb, "would close a cycle"
        self._set(ta, hb)

    def close_deadlines(self, s: int):
        """期限管理: 番地 < s の succ/pred を新鮮な点で埋め、全域化を進める。"""
        for x in range(min(s, self.next_fresh)):
            if x not in self.succ:
                self._set(x, self.fresh())
            if x not in self.pred:
                self._set(self.fresh(), x)

    def same_orbit(self, a: int, b: int) -> bool:
        return self.head(a) == self.head(b)


def demo1_totality():
    cb = ChainBuilder()
    cb.new_chain(3)
    s = 0
    while cb.next_fresh < 150 or s <= 150:   # 段階 s は際限なく進む
        cb.close_deadlines(s)
        s += 1
    for x in range(150):
        assert x in cb.succ and x in cb.pred
    print("demo1 期限管理: OK — 番地 0..149 で f と f^-1 が全域化")


def demo2_realization():
    """実現補題: S の元 e が列挙されたら鎖 A_e と B_e を連結する。
    アンカー a_e, b_e が同軌道 ⟺ e ∈ S。"""
    cb = ChainBuilder()
    S_enum = {3: 5, 7: 11}          # e -> 列挙される段階（S = {3, 7}）
    anchors = {}
    for e in range(10):
        a = cb.new_chain(2)[0]
        b = cb.new_chain(2)[0]
        anchors[e] = (a, b)
    for s in range(30):
        for e, t in S_enum.items():
            if t == s:
                cb.link(anchors[e][0], anchors[e][1])
        cb.close_deadlines(s)
    for e in range(10):
        assert cb.same_orbit(*anchors[e]) == (e in S_enum)
    print("demo2 実現補題: OK — 軌道所属が S ⊆ N をコードした")


def demo3_defeat_honest_reflector():
    """撃破デモ: 「鎖の最小元を中心に反転する」正直な候補 ι を、
    確約後に『より小さい最小元を持つ鎖』を接続して偽にする。

    ι のスナップショット値は確約（計算可能な ι は過去の出力を
    変えられない）。連結後の f で ι f ι = f^-1 を検査する。"""
    cb = ChainBuilder()
    A = cb.new_chain(5)             # 節点 0..4: 最小元 0 を中心と確約させる
    B = cb.new_chain(5)             # 節点 5..9

    def snapshot_reflector(chain: list[int]) -> dict[int, int]:
        b = min(chain)              # 正準中心 = 鎖の最小元
        i = {x: chain[(chain.index(b) - (chain.index(x) - chain.index(b)))
                      % len(chain)] for x in chain}
        return i

    iota = snapshot_reflector(A)    # 段階 s での確約（A だけ見て反転を決めた）
    cb.link(B[0], A[0])             # 敵対者: B の末尾を A の先頭に接続
    # 接続後、A∪B の「正しい」反転中心は変わるが ι の確約は A 基準のまま。
    ok = all(
        iota.get(cb.succ[x]) == cb.pred.get(iota[x])
        for x in A if x in cb.succ and cb.succ[x] in iota and iota[x] in cb.pred
    )
    violated = any(
        x in cb.succ and cb.succ[x] in iota and iota[x] in cb.pred
        and iota[cb.succ[x]] != cb.pred[iota[x]]
        for x in A
    )
    assert violated and not ok
    print("demo3 単一要件の撃破: OK — 連結が確約 ι(f(x)) = f^-1(ι(x)) を破った")


def demo4_defeat_chain_swapper():
    """攻め筋2の核: 鎖を対で交換する型の候補 ι の撃破（定理 7.2 の残ギャップ）.

    ι が鎖 A と B の逆向きアラインメント（A の k 番目 ↔ B の後ろから
    k 番目）を確約したとする。敵対者は A の末尾を新鮮な点 y で延長する。
    反転条件 ι(f(tail A)) = f^-1(ι(tail A)) = f^-1(head B) が成り立つには、
    ι(y) が pred(head B) に一致しなければならないが、pred(head B) は
    まだ未定義で敵対者の手中にある。ι は固定関数なので ι(y) の値は
    延長前に決まっており（確約）、敵対者は観測済みの ι の出力を避けて
    pred(head B) を選べばよい（06 ノートの「観測済み出力を避ける競走」）。"""
    cb = ChainBuilder()
    A = cb.new_chain(4)                     # 0..3
    B = cb.new_chain(4)                     # 4..7
    iota = {A[k]: B[len(B) - 1 - k] for k in range(4)}
    iota.update({v: k for k, v in iota.items()})     # 対合として閉じる

    # 候補 ι の「延長点での値」も固定関数として確約済み（値は何であれ
    # 敵対者の観測対象）。ここでは最悪ケースとして、ι が敵対者の直後の
    # 新鮮値を言い当てようとする戦略を採ったとする。
    predicted = cb.next_fresh + 1
    y = cb.fresh()
    cb._set(A[-1], y)                       # A の末尾を y で延長
    iota[y] = predicted

    observed = set(iota.values())           # 敵対者が観測した ι の出力全体
    u = cb.fresh()
    while u in observed:                    # 観測済み出力を避けて選ぶ
        u = cb.fresh()
    cb._set(u, B[0])                        # pred(head B) := u

    # 反転条件の検査: ι(f(tail A)) = f^-1(ι(tail A)) か？
    lhs = iota[cb.succ[A[-1]]]              # ι(y) — 確約済みの値
    rhs = cb.pred[iota[A[-1]]]              # f^-1(head B) = u — 敵対者の選択
    assert lhs != rhs
    print("demo4 対交換型の撃破: OK — 観測済み出力を避けた選択が確約を破った")


if __name__ == "__main__":
    demo1_totality()
    demo2_realization()
    demo3_defeat_honest_reflector()
    demo4_defeat_chain_swapper()
