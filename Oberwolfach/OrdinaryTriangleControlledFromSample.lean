module

public import Oberwolfach.OrdinaryPackingCleanupFinishEvent
public import Oberwolfach.OrdinaryTriangleControlledCoverDown

@[expose] public section
/-! The three actual same-sample wheel packings form a one-level triangle
cover-down and a balanced divisible inner remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_controlled_cover_down_from_sample_outcome
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) (p τ ν:ℝ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,3∣(Finset.univ.filter (fun v=>H v u)).card)
    (h:OrdinaryPackingCleanupFinishOutcome Q F H X Z σ p τ ν):
    OrdinaryTriangleControlledCoverDownResult Q H X Z ((ν+4*p)*Fintype.card (V⊕U)):=by
  obtain ⟨M,K,hfinish⟩:=h
  let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ
  let A:=ordinaryWheelRimGraph M.wheels
  let S:=ordinaryPackingSpokes M.wheels
  let B:=wheelFamilyRim K.wheels
  let T:=wheelFamilySpokes K.wheels
  have hA:HasOrdinaryWheelDecomposition A S 3:=ordinaryPacking_decomposition M.wheels M.disjoint
  have hB:HasOrdinaryWheelDecomposition B T 3:=K.decomposition
  have hAsub:A≤Q:=(ordinaryWheelRimGraph_subhost M.wheels).trans (sdiff_le.trans sdiff_le)
  have hSsub:∀v u,S v u→H v u:=by
    intro v u hvu
    obtain ⟨W,hW,hu,hv⟩:=hvu
    rw [←hu]
    exact (W.property.1 v hv).1
  have hK:=wheelFamily_subhost K.wheels
  have hBsub:B≤Q\A:=hK.1
  have hTsub:∀v u,T v u→H v u∧¬S v u:=hK.2
  have hm:=ordinary_packing_post_facts Q F H X Z R 3 (τ*Fintype.card (V⊕U)) M hbal hdiv
  exact ordinary_triangle_controlled_cover_down_from_three Q A B H S T X Z p ν hA hB hAsub hSsub hBsub hTsub
    hm.inner_avoided K.degree hfinish

end Oberwolfach
