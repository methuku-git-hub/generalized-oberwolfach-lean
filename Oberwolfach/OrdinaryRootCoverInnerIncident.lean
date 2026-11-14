module

public import Oberwolfach.OrdinaryRootCoverData

@[expose] public section
/-! The cover has small incidence into the enclosing rim set, at both
inside and outside endpoints. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_inner_incident (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (A:OrdinaryRootCoverData Q F H X T Z W r η ell) (a:V⊕U):
    ((X.filter (fun v=>(ordinaryPhysicalGraph A.rim A.spokes).Adj a (Sum.inl v))).card:ℝ)≤max η ell:=by
  let G:=ordinaryPhysicalGraph A.rim A.spokes
  let Y:=X.filter (fun v=>G.Adj a (Sum.inl v))
  by_cases ha:a∈ordinaryInnerVertices X Z
  · let I:=spanningRestriction G (ordinaryInnerVertices X Z)
    have hsub:Y.image (Sum.inl:V→V⊕U)⊆I.neighborFinset a:=by
      intro z hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      have hv':v∈X ∧ G.Adj a (Sum.inl v):=Finset.mem_filter.mp hv
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr
        ((spanningRestriction_adj _ _ _ _).mpr ⟨hv'.2,ha,(ordinaryInnerVertices_left X Z v).mpr hv'.1⟩)
    have hc:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Sum.inl_injective,SimpleGraph.card_neighborFinset_eq_degree] at hc
    have hcR:(Y.card:ℝ)≤(I.degree a:ℝ):=by exact_mod_cast hc
    exact hcR.trans ((A.inner_degree a).trans (le_max_left _ _))
  · have hsub:Y.image (Sum.inl:V→V⊕U)⊆G.neighborFinset a:=by
      intro z hz
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
      exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Finset.mem_filter.mp hv).2
    have hc:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Sum.inl_injective,SimpleGraph.card_neighborFinset_eq_degree] at hc
    have hcR:(Y.card:ℝ)≤(G.degree a:ℝ):=by exact_mod_cast hc
    exact hcR.trans ((A.outside_degree a ha).trans (le_max_right _ _))
end Oberwolfach
