# 対合コンパイラの新規性サーベイ（2026-07-29）

結論: **新規**。「位数有限の可逆プログラムを2つの対合プログラムの
合成へコンパイルする検証済み変換」に先行なし。プロトタイプは
`../invcomp/`。

## 根拠（一次確認済み）

- Nakano 3部作（RC 2020 / MFCS 2021 / SCP 2022）の被引用は計8件
  （S2 引用グラフ）。内訳は Glück–Yokoyama TCS 2022 サーベイ、
  自己引用、BISCUITS 章、VPT 2022、露文カウンタ機械論文、
  PEPM 2025（レンズ）のみ。**コンパイル・変換系はゼロ。**
- 最接近1: Gajardo–Kari–Moreira (JCSS 2012)。CA で F = H∘G
  （対合2つ）の分解可否を研究。差分: 彼らは「どの可逆 CA が分解
  できるか」（できないものがある）、我々は「位数有限なら常に・
  構成的に・検証つきで分解」。関連研究節で明示対置が必須（査読者
  トラップ）。
- 最接近2: Nakano SCP 2022 自身が「時間対称 CA は単一対合でなく
  2対合の合成を計算する」と観察。分解の**アイデア**は彼の系譜に
  内在するので、貢献は「検証済み・構成的・プログラムレベルの変換」
  として立てること。
- 機械化系の近傍: Paolini–Piccolo–Roversi (TYPES 2015, Matita)、
  Amy–Roetteler–Svore ReVerC (CAV 2017, F*)、Choudhury et al.
  (POPL 2022, Agda, rig groupoids)、Kalpis (Agda)。いずれも対合・
  位数構造なし。Axelsen の Janus→PISA (CC 2011) は未検証コンパイラ。
- 要追確認: Kutrib–Worsch (RC 2013) と BISCUITS 章の本文
  （2対合分解の機械構成が無いことの最終確認。全文未入手）。

## must-cite（12件、書誌は S2/DBLP で実在確認済み）

Nakano×3, GKM 2012, Kutrib–Worsch 2013, Choudhury+ POPL 2022,
Heunen–Kaarsgaard–Karvonen 2018（involutive monoid の語の弁別用）,
Paolini+ 2015, Amy+ 2017, Axelsen 2011, Glück–Yokoyama 2022,
Lamb–Roberts 1998。
