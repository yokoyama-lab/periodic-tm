# テーマ03: Bennett 可逆化の Lean 4 機械化

## 問題設定

Bennett (1973) の可逆化は「任意の計算を、履歴テープを使って可逆に実行し、
出力をコピーしてから履歴を逆再生で消す」という構成である。
Python プロトタイプ（`../../bennett_uncompute.py`, `../../bennett_fcu.py`）は
動いている。これを `../../lean/` の機械モデル（`MultiTape.lean` の k テープ
機械と `KFlipOf` による時間反転）の上で定理として証明するのがゴール。

## 最初の一歩

1. `lean/` をビルドし（`lake exe cache get && lake build`）、
   `FiniteOrderTM/Copy.lean` と `FiniteOrderTM/Flip.lean` を読む。
   コピー機械と逆再生という部品はすでに証明済みで揃っている。
2. `python3 ../../bennett_uncompute.py` で構成の各フェーズ
   （compute → copy → uncompute）の配置を確認する。
3. `Exercises.lean` の `sorry` を上から順に埋める（易→難の順に並べてある。
   これは演習用ファイルで、本体のビルド対象には含まれていない）。

## マイルストーン

- [ ] Exercises.lean の演習を全部埋める（対合・逆再生の基本操作）
- [ ] compute–copy–uncompute の 3 フェーズ合成を `Compose.lean` の
      直列合成で定式化する
- [ ] 主定理「任意の計算可能関数 f に対し x ↦ (x, f x) は可逆機械で
      計算できる」を述べて証明する
