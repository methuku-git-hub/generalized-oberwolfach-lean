module

public import Oberwolfach.OrdinarySequentialWheelDecomposition

@[expose] public section
/-! Three wheel packings in successive remainders form one decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_three_sequential_wheel_decompositions
    (Q A B C:SimpleGraph V) (H S T W:V→U→Prop) (r:ℕ)
    (hA:HasOrdinaryWheelDecomposition A S r) (hB:HasOrdinaryWheelDecomposition B T r)
    (hC:HasOrdinaryWheelDecomposition C W r)
    (hBsub:B≤Q\A) (hTsub:∀v u,T v u→H v u∧¬S v u)
    (hCsub:C≤(Q\A)\B) (hWsub:∀v u,W v u→(H v u∧¬S v u)∧¬T v u):
    HasOrdinaryWheelDecomposition ((A⊔B)⊔C) (fun v u=>(S v u∨T v u)∨W v u) r ∧
    Q\((A⊔B)⊔C)=((Q\A)\B)\C ∧
    (∀v u,(H v u∧¬((S v u∨T v u)∨W v u))↔(((H v u∧¬S v u)∧¬T v u)∧¬W v u)):=by
  have hAB:=ordinary_sequential_wheel_decomposition Q A B H S T r hA hB hBsub hTsub
  have hCsub':C≤Q\(A⊔B):=by rw [hAB.2.1];exact hCsub
  have hWsub':∀v u,W v u→H v u∧¬(S v u∨T v u):=by
    intro v u hw
    have hh:=hWsub v u hw
    tauto
  have hABC:=ordinary_sequential_wheel_decomposition Q (A⊔B) C H (fun v u=>S v u∨T v u) W r
    hAB.1 hC hCsub' hWsub'
  refine ⟨hABC.1,?_,?_⟩
  · rw [hABC.2.1,hAB.2.1]
  · intro v u
    tauto
theorem ordinary_three_sequential_decompositions_in_host
    (Q A B C:SimpleGraph V) (H S T W:V→U→Prop) (r:ℕ)
    (hA:HasOrdinaryWheelDecomposition A S r) (hB:HasOrdinaryWheelDecomposition B T r)
    (hC:HasOrdinaryWheelDecomposition C W r)
    (hAsub:A≤Q) (hSsub:∀v u,S v u→H v u)
    (hBsub:B≤Q\A) (hTsub:∀v u,T v u→H v u∧¬S v u)
    (hCsub:C≤(Q\A)\B) (hWsub:∀v u,W v u→(H v u∧¬S v u)∧¬T v u):
    ((A⊔B)⊔C)≤Q ∧ (∀v u,(S v u∨T v u)∨W v u→H v u) ∧
    HasOrdinaryWheelDecomposition ((A⊔B)⊔C) (fun v u=>(S v u∨T v u)∨W v u) r ∧
    Q\((A⊔B)⊔C)=((Q\A)\B)\C ∧
    (∀v u,(H v u∧¬((S v u∨T v u)∨W v u))↔(((H v u∧¬S v u)∧¬T v u)∧¬W v u)):=by
  have hdec:=ordinary_three_sequential_wheel_decompositions Q A B C H S T W r hA hB hC hBsub hTsub hCsub hWsub
  refine ⟨sup_le (sup_le hAsub (hBsub.trans sdiff_le)) (hCsub.trans (sdiff_le.trans sdiff_le)),?_,hdec.1,hdec.2.1,hdec.2.2⟩
  intro v u hvu
  rcases hvu with (hS|hT)|hW
  · exact hSsub v u hS
  · exact (hTsub v u hT).1
  · exact ((hWsub v u hW).1).1
end Oberwolfach
