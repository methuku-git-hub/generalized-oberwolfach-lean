module

public import Oberwolfach.OrdinaryExactDecomposition

@[expose] public section
/-! Wheel decompositions chosen successively in the actual remainder combine
into one decomposition with an exact final rim and spoke remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sequential_wheel_decompositions
    (Q R₁ R₂ R₃:SimpleGraph V) (H S₁ S₂ S₃:V→U→Prop) (r:ℕ)
    (hR₂:R₂≤Q\R₁) (hR₃:R₃≤(Q\R₁)\R₂)
    (hS₂:∀v u,S₂ v u→H v u∧¬S₁ v u)
    (hS₃:∀v u,S₃ v u→(H v u∧¬S₁ v u)∧¬S₂ v u)
    (hdec₁:HasOrdinaryWheelDecomposition R₁ S₁ r)
    (hdec₂:HasOrdinaryWheelDecomposition R₂ S₂ r)
    (hdec₃:HasOrdinaryWheelDecomposition R₃ S₃ r):
    HasOrdinaryWheelDecomposition ((R₁⊔R₂)⊔R₃) (fun v u=>(S₁ v u∨S₂ v u)∨S₃ v u) r ∧
    Q\((R₁⊔R₂)⊔R₃)=((Q\R₁)\R₂)\R₃ ∧
    (fun v u=>H v u∧¬((S₁ v u∨S₂ v u)∨S₃ v u))=
      (fun v u=>((H v u∧¬S₁ v u)∧¬S₂ v u)∧¬S₃ v u):=by
  have hdis₁₂:Disjoint R₁ R₂:=by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact (hR₂ h.2).2 h.1
  have hsdis₁₂:∀v u,¬(S₁ v u∧S₂ v u):=by
    intro v u h
    exact (hS₂ v u h.2).2 h.1
  have hdec₁₂:=ordinary_wheel_decomposition_union R₁ R₂ S₁ S₂ r hdec₁ hdec₂ hdis₁₂ hsdis₁₂
  have hdis₁₂₃:Disjoint (R₁⊔R₂) R₃:=by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    have hh:=hR₃ h.2
    rcases h.1 with h₁|h₂
    · exact hh.1.2 h₁
    · exact hh.2 h₂
  have hsdis₁₂₃:∀v u,¬((S₁ v u∨S₂ v u)∧S₃ v u):=by
    intro v u h
    have hh:=hS₃ v u h.2
    rcases h.1 with h₁|h₂
    · exact hh.1.2 h₁
    · exact hh.2 h₂
  refine ⟨ordinary_wheel_decomposition_union (R₁⊔R₂) R₃ (fun v u=>S₁ v u∨S₂ v u) S₃ r
    hdec₁₂ hdec₃ hdis₁₂₃ hsdis₁₂₃,?_,?_⟩
  · ext v w
    simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
    tauto
  · funext v u
    apply propext
    tauto
end Oberwolfach
