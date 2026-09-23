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
| ゲーム値の小例 | 値=1 (N5,ℓ3)・値=2 (N6/7,ℓ4) | **1 [Lean済]**（`native_decide`） | `QueryGame.lean` native_decide 5件。公理 `Lean.ofReduceBool` に依存（コンパイル済み評価を信用）。`AuditQueryGame.lean` で監査 |
| 定理 7.3 | 軌道決定可能 ⟹ 2対合の積 | **1 [Lean済]**（構造核のみ） | `PermTwoInvolutions.lean`: 任意の置換と軌道データ（代表・位置）から `ι₂ x = f^(−pos x)(rep x)`, `ι₁ = f∘ι₂` が対合で `ι₁∘ι₂ = f`（`perm_eq_two_involutions_of_rep`）。**軌道決定可能性から代表・位置を計算する有効性の層は層2のまま**（research/07, Boege 4.4 経由） |
| 補題 7.1 / 定理 7.2 | 中心抽出・免疫置換の反転対合は固定有限本 | **1 [Lean済]**（抽象形） | `CenterExtraction.lean`: 補題 7.1 `exists_center`、中心の一意性 `center_unique`、定理 7.2 は「サイクル免疫（無限 c.e. 集合は同一サイクルに 2 点を含む）」を仮定とする抽象形 `fixed_orbits_finite` と ℕ 上 `fixed_orbits_finite_of_computable`（中心集合の決定可能性を mathlib `Computable`/`REPred` で証明）。**Higman 置換の存在（免疫性）は文献入力のまま** |
| 定理 9.6 | 2点ゲーム値 = min(ℓ−2, k₁\*) | 2 [紙証明] | 上界・下界とも紙。数値は45セル二重検証（claimA_check / gen_value_table） |
| 補題 9.7 主張A | 別軌道実行可能性の区間条件（下界領域限定） | 2 [紙証明] | 領域内70状態で式・brute・実行可能性が三重一致。領域外では偽（既知反例8件） |
| 定理 11.1 | 鏡映複製（免疫＋反転対合の共存） | **1 [Lean済]** | `Doubling.lean` `mirror_doubling`: 免疫・自由・計算可能（逆も）な ρ から ρ̂ の計算可能性・自由性・免疫性の遺伝（`REPred` 版）・面交換 ι の対合性/反転性/固定鎖ゼロを全て Lean 化。**Higman 置換 ρ₀ の存在は文献入力**（doubling_check.py の数値検査は独立確認として残る） |
| 定理 13.1 | 半シフト補正（問Bの特徴づけ） | **1 [Lean済]**（有限軌道なしの場合） | `HalfShift.lean`: `ι x = g(f^(−⌈t/2⌉) x)` の対合性・反転性 `half_shift_correction`、自由置換では側条件を導出 `half_shift_correction_free`、問B `strongly_reversible_iff_orbit_involutive_reverser`。**有限軌道との貼り合わせ（定理 4.1 経由）は未機械化**（有限軌道のみなら `LocallyFinite.lean` が担う） |
| 定理 3.1（核分解の特徴づけ） | 核分解 ⟺ Im(f^m) 決定可能 | **1 [Lean済]**（(ii)⟹(i) 完全、(i)⟹(ii) は構造核） | `KernelDecomp.lean`: (ii)⟹(i) `core_decidable_of_kernel_decomp`（mathlib `Computable`）、(i)⟹(ii) の射影 `e` と核分解の存在 `kernel_decomp_exists`、観察 3.0 `three_factor_forces_indexOne`。**(i)⟹(ii) の e, ι₁, ι₂ の計算可能性は層2のまま**（定理 4.1 の効果性と同じ扱い） |
| 定理 12.1 | 統合構成（免疫＋逆元非共役） | **3 [骨格]** | 干渉解析 (a)–(d) は書いたが、Higman 3.1/3.6 の構成細部への依存が深く優先度法の網羅は未完 |
| 予想 13.2 | 問C は否定的 | 3 [予想] | 構成方針のみ |
| 予想 1.0 | n ≥ 3 の三条件不可能性 | 3 [予想] | 証拠3件と証明計画のみ |
| Higman 帰結（G 非 strongly real） | 定理 3.7(ii) の m=1, n=−1 | 文献 | 原典精読済み。帰結の導出（4行の代数）は層2 |
| コンパイラ正当性 | compile_correct / involutive₁₂ / spec | **1 [Lean済]** | `InvComp.lean`（深い埋め込み・Perm 着地） |
| ITM 1マス完全性 | writeHead iff・completenessGoal_oneCell | **1 [Lean済]** | `Involutory.lean` |
| 文字列橋渡し | StringInvolutory・閉包(a)・applyHead 橋 | **1 [Lean済]** | `InvolutoryString.lean` |
| KMachine⇔TM0 輸送 | 双模倣 ofK/toK・共役合成の構文的対合性 | **1 [Lean済]** | `InvolutoryTransport.lean` |

## 影響範囲の注記

- 短報 `note-strongly-real.tex` には層2・3の定理が断定調で含まれる。
  **投稿前に層ラベルに従い本文の主張水準を再点検すること**
  （特に統合構成の段落は層3であり、"can moreover be run" の断定は要弱化）。
- 過去の研究ノート（07, 09, 11, 12, 13）の「証明済み」表記は本台帳が優先する。
  ノート側の表記は順次この台帳へのリンクに置き換える。
