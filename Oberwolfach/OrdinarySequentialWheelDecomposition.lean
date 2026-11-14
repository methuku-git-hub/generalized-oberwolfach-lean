module

public import Oberwolfach.OrdinaryExactDecomposition

@[expose] public section
/-! Wheel decompositions selected successively in the actual remainder join
into one decomposition, with the same final rim and spoke remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sequential_wheel_decomposition
    (Q A B:SimpleGraph V) (H S T:V→U→Prop) (r:ℕ)
    (hA:HasOrdinaryWheelDecomposition A S r) (hB:HasOrdinaryWheelDecomposition B T r)
    (hBsub:B≤Q\A) (hTsub:∀v u,T v u→H v u∧¬S v u):
    HasOrdinaryWheelDecomposition (A⊔B) (fun v u=>S v u∨T v u) r ∧
    Q\(A⊔B)=(Q\A)\B ∧
    (∀v u,(H v u∧¬(S v u∨T v u))↔((H v u∧¬S v u)∧¬T v u)):=by
  have hAB:Disjoint A B:=by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact (hBsub h.2).2 h.1
  have hST:∀v u,¬(S v u∧T v u):=by
    intro v u h
    exact (hTsub v u h.2).2 h.1
  refine ⟨ordinary_wheel_decomposition_union A B S T r hA hB hAB hST,?_,?_⟩
  · ext v w
    simp [SimpleGraph.sdiff_adj]
    tauto
  · intro v u
    tauto
end Oberwolfach
