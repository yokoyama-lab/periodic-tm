import FiniteOrderTM.Basic
import FiniteOrderTM.LocallyFinite
import FiniteOrderTM.InvComp
import FiniteOrderTM.Dihedral
import FiniteOrderTM.Machine
import FiniteOrderTM.Involutory
import FiniteOrderTM.MultiTape
import FiniteOrderTM.PrePeriod
import FiniteOrderTM.Compose
import FiniteOrderTM.Lift
import FiniteOrderTM.Flip
import FiniteOrderTM.Symmetrise
import FiniteOrderTM.Completeness
import FiniteOrderTM.SemReversible
import FiniteOrderTM.Reindex
import FiniteOrderTM.Copy
import FiniteOrderTM.CopyMulti
import FiniteOrderTM.CopyMultiFold
import FiniteOrderTM.CopyMultiK
import FiniteOrderTM.IOConvention
import FiniteOrderTM.IOConventionInstance
import FiniteOrderTM.InvolutoryString
import FiniteOrderTM.InvolutoryTransport
import FiniteOrderTM.InvolutoryBennett
import FiniteOrderTM.HistoryMachine
import FiniteOrderTM.InvolutoryAssembly
import FiniteOrderTM.NoGo
import FiniteOrderTM.TwoPointCore
import FiniteOrderTM.TwoPointClaimA
-- 定理9.6 の下界の本体。root から import していないと `lake build` の対象外になり、
-- 「lake build 緑」が two_point_lower_bound について何も言わない状態になる
-- （2026-08-10 に是正。それまでは `lake env lean` の一回限りの検査で、olean も CI も残っていなかった）。
import FiniteOrderTM.TwoPointLowerBound
-- 定理9.6 の上界の部品（軌道保存反射の存在）。2026-08-10 に作られたが root から
-- 取り込まれておらず、11 晩ずっと `lake build` の対象外だった（2026-08-21 に是正）。
import FiniteOrderTM.TwoPointReflect
-- 定理9.6 の上界の本体と、上界＋下界を合わせた値の公式。
import FiniteOrderTM.TwoPointUpper
-- 検査は走らせないと「異常なし」と区別がつかないので、native_decide の
-- 証明書ファイルも root から取り込む（実測の追加コストはキャッシュが無い
-- 場合の一度きり: Cert=138s, ClaimACert=472s。2026-08-21）。
import FiniteOrderTM.TwoPointUpperCert
import FiniteOrderTM.TwoPointClaimACert
-- 定理9.6 のオラクル約束が非空になる範囲 (`0 < ℓ ≤ N`) の確定。上下界の
-- 議論が実質を持つ場所を切り分ける。root import 漏れは前例があるので
-- 最初から入れておく。
import FiniteOrderTM.TwoPointNonvacuous
