# 検証状態台帳（正本）

運用ルール（2026-07-28 決定）: **「確定」を名乗れるのは層1のみ。**

- **層1 [Lean済]** — sorry ゼロで lake build が通る機械証明。確定。
- **層2 [紙証明]** — Claude が書き下し検算した紙の証明。未機械化。
  指導教員のレビューか機械化を経るまで断定しない。
- **層3 [骨格]** — 証明の骨格＋機械実験の裏付けのみ。実質は予想。

| 結果 | 内容 | 層 | 根拠 |
|---|---|---|---|
| 定理 4.1 | 局所有限 ⟹ 2対合の積（数学的核） | **1 [Lean済]** | `LocallyFinite.lean`（効果性の議論は層2） |
| 補題 9.4 | 恒真型出力対の4型分類 | **1 [Lean済]** | `TwoPointCore.lean`（ZMod 上の抽象版） |
| k₁\* の特徴づけ | kills ⟺ minDivGe 条件 | **1 [Lean済]** | `TwoPointCore.lean` |
| ゲーム値の小例 | 値=1 (N5,ℓ3)・値=2 (N6/7,ℓ4) | **1 [Lean済]** | `QueryGame.lean` native_decide 5件 |
| 定理 7.3 | 軌道決定可能 ⟹ 2対合の積 | 2 [紙証明] | research/07（Boege 4.4 経由） |
| 補題 7.1 / 定理 7.2 | 中心抽出・免疫置換の反転対合は固定有限本 | 2 [紙証明] | research/07（間引きは Higman Lemma 3.3 引用） |
| 定理 9.6 | 2点ゲーム値 = min(ℓ−2, k₁\*) | 2 [紙証明]（**要人間判定: この行の層ラベルは古い**） | ⚠ 根拠欄の「上界・下界とも紙」は**事実に反する**（2026-08-21 訂正）。下界は 08-10 に、上界は 08-21 に機械化済みで、値の公式まで Lean に載っている（下の 2 行を参照）。数値は45セル二重検証（claimA_check / gen_value_table）。層ラベルの更新は人間のレビュー事項なので触っていない |
| 補題 9.7 主張A | 別軌道実行可能性の区間条件（下界領域限定） | 2 [紙証明] | 領域内70状態で式・brute・実行可能性が三重一致。領域外では偽（既知反例8件） |
| 定理 11.1 | 鏡映複製（免疫＋反転対合の共存） | 2 [紙証明] | 等式は doubling_check.py で機械検査。免疫性の遺伝は紙 |
| 定理 13.1 | 半シフト補正（問Bの特徴づけ） | 2 [紙証明] | 恒等式＋トイモデル機械検査。一般証明は紙 |
| 定理 3.1（核分解の特徴づけ） | 核分解 ⟺ Im(f^m) 決定可能 | 2 [紙証明] | research/03 |
| 定理 12.1 | 統合構成（免疫＋逆元非共役） | **3 [骨格]** | 干渉解析 (a)–(d) は書いたが、Higman 3.1/3.6 の構成細部への依存が深く優先度法の網羅は未完 |
| 予想 13.2 | 問C は否定的 | 3 [予想] | 構成方針のみ |
| 予想 1.0 | n ≥ 3 の三条件不可能性 | 3 [予想] | 証拠3件と証明計画のみ |
| Higman 帰結（G 非 strongly real） | 定理 3.7(ii) の m=1, n=−1 | 文献 | 原典精読済み。帰結の導出（4行の代数）は層2 |
| コンパイラ正当性 | compile_correct / involutive₁₂ / spec | **1 [Lean済]** | `InvComp.lean`（深い埋め込み・Perm 着地） |
| ITM 1マス完全性 | writeHead iff・completenessGoal_oneCell | **1 [Lean済]** | `Involutory.lean` |
| 文字列橋渡し | StringInvolutory・閉包(a)・applyHead 橋 | **1 [Lean済]** | `InvolutoryString.lean` |
| KMachine⇔TM0 輸送 | 双模倣 ofK/toK・共役合成の構文的対合性 | **1 [Lean済]** | `InvolutoryTransport.lean` |
| 定理9.6 下界の葉での撃墜（具体側） | 型3は別軌道完成で（`type3_output_killed`）、型1・2・4 は距離 d と d+1 の同一軌道完成2本で（`type{1,2,4}_killed_two_distances`）死ぬ。同一軌道完成の構成（`sameCyclePerm_isCompletion`）と距離の実現（`sameCyclePerm_pow_eq_one_vertex`）も済み | **1 [Lean済]** | `TwoPointAdversary.lean`（※「root 非取込」は誤り。`TwoPointConcrete` 経由で `lake build` の対象。2026-08-21 訂正）。残るのは木の帰納の最終段のみ。ただし頂点番号がグループ順のため状態成長で動く問題があり、付け替え（relabeling）の輸送補題が要る（`research/17`）|
| 定理9.6 の橋渡し（roadmap 1・2） | 位置座標 `f^i x = f^j x ↔ (i:ZMod ℓ)=j`／反射の共役関係／反射の出力対が `SameCycleValid`（＝補題9.4 の有効性条件）を満たすこと | **1 [Lean済]** | `TwoPointBridge.lean`（※「root 非取込」は誤り。現在は `lake build` の対象。2026-08-21 訂正）。これで型分類 type1〜4 が具体側の出力対に適用可能。残るは Tree 帰納（roadmap 5）と上界の構成（6） |
| 下界の不変量(2)＋主張B（下界形） | 領域内では別軌道完成が必ず生存（型3恒真対を殺せる）／別軌道を殺すには q ≥ min(ℓ−2, k₁\*) | **1 [Lean済]** | `TwoPointClaimAGeneral.lean` の `completion_survives` / `kill_cost_ge`（主張A一般形の系） |
| **補題 9.7 主張A（一般）** | 下界領域内で FormulaSide ↔ CompletionSide。(⇒) は領域条件のみから、(⇐) はパッキング構成（k₁\* 選択・2ビン貪欲・充填＝未開示点の連続区間） | **1 [Lean済]** | `TwoPointClaimAGeneral.lean`（sorry 0・公理は propext/Classical.choice/Quot.sound のみ、末尾の `#print axioms` が毎回確認）。※「root 非取込」は誤りで、現在は `lake build` の対象（2026-08-21 訂正） |
| **定理9.6 下界（一般）** | `two_point_lower_bound`: q < min(ℓ−2, k₁\*) ⇒ 深さ q の適応木は勝てない。新鮮応答敵対者の具体対局（ConcState）＋付け替え τ の輸送＋2距離同一軌道完成（迷い溢れは2サイクル化）＋配置内訳つき別軌道完成で、葉の全出力対を撃墜（research/18 の表） | **1 [Lean済]**（層ラベルは要人間レビュー） | `TwoPointLowerBound.lean`（`lake build` 対象。native_decide 不使用・公理は標準3つ。部品: `TwoPointRelabel/Concrete/Transport/SameCycle/DiffCycle.lean`、2026-08-10 夜間 autoresearch）。※この欄は 08-20 まで「root 非取込」と書いていたが 8bacb1d 以降**誤り**だった（2026-08-21 訂正） |
| **定理9.6 上界（一般）** | `two_point_upper_bound`: 深さ `min(ℓ−2, k₁\*)` の勝利木が存在する。2 ルート: (i) ピン留め `walkZero`（0 から ℓ−2 歩。1 を見なければ「別軌道」か「1 = f^(ℓ−1)0」に落ち、出力 `(f^(ℓ−2)0, 1)` が両方で良い）、(ii) 別軌道殺し `walkOne`（1 から k₁\* 歩。閉じず 0 にも触れなければ 1 の軌道長が `Kills` の空窓に入り別軌道が死ぬ） | **要人間判定**<br>（機械側の事実: sorry 0 で `lake build` 通過） | `TwoPointUpper.lean`（root 取込・`lake build` 対象。sorry 0・native_decide 不使用・公理は標準3つ）。葉の出力が本質的であることは変異注入で確認（`TwoPointUpperCert.lean`、層2）。2026-08-21 夜間 autoresearch |
| **定理9.6（値の公式）** | `gameValue_eq`: `gameValue N ℓ = min(ℓ−2, k₁\*(N,ℓ))`（`gameValue` = 勝利木が存在する最小の深さ）。上界＋下界の合成で、紙の定理9.6 そのもの | **要人間判定**<br>（機械側の事実: sorry 0 で `lake build` 通過） | `TwoPointUpper.lean` の `gameValue_eq` / `two_point_value`。閉形式が厳密ソルバの測定42セルに一致することも `decide` で検査（`closed_form_matches_measured`）。公理監査 `Audit.lean` が `lake build` で毎回確認 |
| 補題 9.7 主張A の定式化＋有界検証 | 式側・全数側を可判定述語として定式化。**領域内全70状態**（claimA_check.py の OK=70 と同数・照合済み）で両側成立: N≤8 は Perm 全数（26）、N∈{9,10} は証人方式（44。python 生成の完成を Lean が1件ずつ検査、被覆は別途決定）。領域外の既知反例 (N6ℓ4, strays=[1,1]) で式≠全数を再現 | **1 [Lean済]**（有界） | `TwoPointClaimA.lean`（記号・root取込）＋ `TwoPointClaimACert.lean`（native_decide。**2026-08-20 まで root 非取込で一度も夜間 run で走っていなかった**。08-21 に root へ入れ、`lake build` で毎回走る）。一般証明（パッキング論法）は未着手 |

## 影響範囲の注記

- 短報 `note-strongly-real.tex` には層2・3の定理が断定調で含まれる。
  **投稿前に層ラベルに従い本文の主張水準を再点検すること**
  （特に統合構成の段落は層3であり、"can moreover be run" の断定は要弱化）。
- 過去の研究ノート（07, 09, 11, 12, 13）の「証明済み」表記は本台帳が優先する。
  ノート側の表記は順次この台帳へのリンクに置き換える。
