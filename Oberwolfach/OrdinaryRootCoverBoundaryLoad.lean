module

public import Oberwolfach.OrdinaryRootCoverNonrootData

@[expose] public section
/-! Covering an enlarged root forces the cover to contain every boundary
spoke at that root. A small full-degree nonroot bound therefore cannot be
inferred by merely relabelling that root as a nonroot. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_row_boundary_load
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (v:V) (hv:v∈T):
    (Finset.univ.filter (fun u=>u∉Z∧H v u)).card≤
      (ordinaryPhysicalGraph D.rim D.spokes).degree (Sum.inl v):=by
  let A:=Finset.univ.filter (fun u=>u∉Z∧H v u)
  have hsub:A.image Sum.inr⊆(ordinaryPhysicalGraph D.rim D.spokes).neighborFinset (Sum.inl v):=by
    intro z hz
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
    rw [SimpleGraph.mem_neighborFinset]
    have hh: u∉Z∧H v u:=(Finset.mem_filter.mp hu).2
    exact D.covers_row v hv u hh.1 hh.2
  calc
    A.card=(A.image Sum.inr).card := by rw [Finset.card_image_of_injective _ Sum.inr_injective]
    _≤((ordinaryPhysicalGraph D.rim D.spokes).neighborFinset (Sum.inl v)).card:=Finset.card_le_card hsub
    _=(ordinaryPhysicalGraph D.rim D.spokes).degree (Sum.inl v):=SimpleGraph.card_neighborFinset_eq_degree _ _

theorem ordinary_root_cover_column_boundary_load
    (Q F:SimpleGraph V) (H:V→U→Prop) (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (D:OrdinaryRootCoverData Q F H X T Z W r η ell) (u:U) (hu:u∈W):
    (Finset.univ.filter (fun v=>v∉X∧H v u)).card≤
      (ordinaryPhysicalGraph D.rim D.spokes).degree (Sum.inr u):=by
  let A:=Finset.univ.filter (fun v=>v∉X∧H v u)
  have hsub:A.image Sum.inl⊆(ordinaryPhysicalGraph D.rim D.spokes).neighborFinset (Sum.inr u):=by
    intro z hz
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hz
    rw [SimpleGraph.mem_neighborFinset]
    have hh: v∉X∧H v u:=(Finset.mem_filter.mp hv).2
    exact D.covers_column u hu v hh.1 hh.2
  calc
    A.card=(A.image Sum.inl).card := by rw [Finset.card_image_of_injective _ Sum.inl_injective]
    _≤((ordinaryPhysicalGraph D.rim D.spokes).neighborFinset (Sum.inr u)).card:=Finset.card_le_card hsub
    _=(ordinaryPhysicalGraph D.rim D.spokes).degree (Sum.inr u):=SimpleGraph.card_neighborFinset_eq_degree _ _
end Oberwolfach
