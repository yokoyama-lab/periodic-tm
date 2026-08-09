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
