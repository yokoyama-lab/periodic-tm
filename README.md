# periodic-tm — 周期的 Turing 機械（Periodic Turing Machines）

可逆計算の一分野である **対合的 Turing 機械（Involutory Turing Machines, ITM）** を
「周期」という観点から一般化する研究プロジェクトです。卒業研究のテーマ候補として
公開しています。Python によるプロトタイプと、**Lean 4 / mathlib による機械化証明**を
同梱しています。

## Nakano の研究はなぜ面白いか

出発点は Nakano による一連の研究です。

- K. Nakano, *Involutory Turing Machines* (RC 2020)
- K. Nakano, *Idempotent Turing Machines* (MFCS 2021)
- K. Nakano, *Time-symmetric Turing machines for computable involutions* (2022)

ITM は「機械そのものが対合（involution）である」— すなわち同じ機械を 2 回走らせると
恒等写像になる（f ∘ f = id）— という制約を課した Turing 機械で、Nakano は
**計算可能な対合はすべて ITM で計算できる**（完全性）を示しました。

私たちがこの結果をとても面白いと思った理由は次の 3 点です。

1. **意味論的性質が構文的制約で完全に捉えられている。**
   「f² = id」という関数（意味論）の性質を、機械の遷移規則の対称性（構文）だけで
   特徴づけている。こうした「意味と構文の一致」が成り立つ例は貴重で、
   可逆プログラミング言語の設計原理そのものに直結する。
2. **証明の核が時間反転という物理的な直観に基づく。**
   完全性証明は「可逆な計算の実行を逆再生すると逆関数が計算される」という
   Lecerf 反転を使う。逆再生と対合（2 回で元に戻る）が Z/2 の構造としてぴったり
   噛み合うのが証明の急所で、美しい。
3. **すぐに次の問いが立つ。**
   対合は「位数 2」の写像である。では位数 3 は？ 位数 n は？
   f^{m+p} = f^m を満たす「(m,p)-周期的」な関数は？ — 自然な一般化の階層が
   目の前に広がっており、卒研規模で新規性のある問いを切り出しやすい。

## コアとなるアイデア

素朴な予想は「Z/n の状態対称性を持つ機械が位数 n の関数をすべて計算する」でした。
しかしこれは**うまくいきません**。Nakano の証明が使う時間反転は Z/2 特有のもので、
「実行を 1/3 だけ逆再生する」ことに対応物がないためです（この no-go の分析も
本プロジェクトの成果の一部です）。

代わりに成り立つのが本プロジェクトの中心定理です。

> **二対合分解定理**: 位数有限の計算可能な全単射 f（fⁿ = id）は、
> 計算可能な 2 つの対合の合成 f = ι₁ ∘ ι₂ に**効果的に**分解できる。

各軌道（orbit）の長さが n 以下で列挙可能であることから、軌道ごとに
「折り返し」の対合を 2 つ構成する、というのが証明の骨子です
（`finite_order.py` で位数 3・位数 6 の具体例を実行して確認できます）。

この定理の帰結として、**ITM は有限位数の可逆計算の「基底」をなす**ことが分かります。
これは Gajardo–Kari–Moreira（JCSS 2012）の「時間対称 ⟺ 2 つの対合の積」という
力学系の古典的結果の、計算可能・有限位数版という位置づけです。逆向きは成り立たない
（2 つの対合の積は無限位数になりうる）ため有限位数はその真部分クラスであり、
「位数 n をネイティブに実現する単一機械モデルは何か」が未解決問題として残ります。

さらに、周期だけでなく前周期（pre-period）を持つ場合の
f = ι₁ ∘ ι₂ ∘ e（e は冪等）への分解（`preperiod.py`）や、
前周期 2 以上では同様の分解が停止性の壁で不可能になる no-go 定理も扱っています。

## Lean 4 による機械化証明

`lean/` は Lean 4 + mathlib の lake プロジェクトで、上記の定理群を機械化しています。

```bash
cd lean
lake exe cache get   # mathlib のビルド済み olean を取得（初回のみ）
lake build
```

主な内容（詳細は `lean/README.md` のファイルマップ参照）:

- `FiniteOrderTM/Basic.lean` — 二対合分解定理 `finite_order_eq_two_involutions`
- `FiniteOrderTM/PrePeriod.lean` — 前周期 1 の分解 `index_one_decomp`
- `FiniteOrderTM/Machine.lean` / `MultiTape.lean` — 単テープ・k テープ機械の
  時間反転（Lecerf 反転）と健全性
- `FiniteOrderTM/NoGo.lean` — 前周期 2 の no-go 定理（停止問題への帰着）
- `FiniteOrderTM/Bennett*.lean` — Bennett 可逆化の機械化（一部進行中、`sorry` を含む）

公理監査は `lake env lean Audit.lean` で実行でき、主要定理は mathlib 標準の公理
（`propext`, `Classical.choice`, `Quot.sound`）のみに依存します。

## 関連研究（フォローすべき文献）

- **可逆計算の古典**
  - Y. Lecerf, *Machines de Turing réversibles* (1963) — 時間反転の原型
  - C. H. Bennett, *Logical Reversibility of Computation* (1973) — 可逆化と履歴消去
  - K. Morita, *Theory of Reversible Computing* (Springer, 2017) — 体系的教科書
- **時間対称性と対合分解**
  - A. Gajardo, J. Kari, A. Moreira, *On time-symmetry in cellular automata* (JCSS 2012)
    — 「時間対称 ⟺ 2 対合の積」。本プロジェクトの分解定理の力学系側の対応物
- **可逆プログラミング言語の意味論**
  - H. B. Axelsen, R. Glück, *What Do Reversible Programs Compute?* (FoSSaCS 2011)
  - V. Choudhury et al., *Symmetries in Reversible Programming* (POPL 2022)
- **Turing 機械・可逆回路の形式検証**
  - Y. Forster et al., *Verified Programming of Turing Machines in Coq* (CPP 2020)
  - M. Amy et al., *Verified Compilation of Space-Efficient Reversible Circuits* (CAV 2017)

## 卒研テーマの例

- 位数 n をネイティブに実現する単一機械モデルの設計と完全性証明（未解決問題）
- 二対合分解の計算量解析（分解で得られる ι₁, ι₂ の効率）
- `Bennett*.lean` の進行中の機械化を完成させる（Lean 4 / mathlib 実践）
- 周期的 Turing 機械のシミュレータ実装と可視化

## ディレクトリ構成

| パス | 内容 |
|---|---|
| `finite_order.py` | 二対合分解のプロトタイプ（位数 3・6 の実例で検証） |
| `preperiod.py` | 前周期付き分解 f = ι₁ ∘ ι₂ ∘ e のプロトタイプ |
| `bennett_uncompute.py`, `bennett_fcu.py`, `copy_str.py` | Bennett 可逆化まわりの実験 |
| `lean/` | Lean 4 / mathlib 機械化（lake プロジェクト） |
