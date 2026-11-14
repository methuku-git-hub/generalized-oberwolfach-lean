module

public import Oberwolfach.OrdinaryBoundaryRootSets

@[expose] public section
/-! A rim-only conflict graph has the same degrees on rim vertices and zero
degree on hub vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_conflict_degree (F:SimpleGraph V) (L:ℝ) (hL:0≤L)
    (hF:∀v,(F.degree v:ℝ)≤L):
    ∀z:V⊕U,((ordinaryPhysicalGraph F (fun _ _=>False)).degree z:ℝ)≤L:=by
  intro z
  cases z with
  | inl v=>
    have he:(ordinaryPhysicalGraph F (fun _ _=>False)).neighborFinset (Sum.inl v:V⊕U)=
        (F.neighborFinset v).image (Sum.inl:V→V⊕U):=by
      ext w
      cases w <;> simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
    rw [←SimpleGraph.card_neighborFinset_eq_degree,he,Finset.card_image_of_injective _ Sum.inl_injective,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact hF v
  | inr u=>
    have he:(ordinaryPhysicalGraph F (fun _ _=>False)).neighborFinset (Sum.inr u:V⊕U)=∅:=by
      ext w
      cases w <;> simp [ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
    rw [←SimpleGraph.card_neighborFinset_eq_degree,he]
    simpa using hL
end Oberwolfach
