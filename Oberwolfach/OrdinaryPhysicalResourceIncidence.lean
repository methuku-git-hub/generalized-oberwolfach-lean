module

public import Oberwolfach.OrdinarySparseResourceCardinality
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! Physical graph degrees control both the local incidence and total number
of any contained ordinary resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_resources_from_physical_degree (Q:SimpleGraph V) (H:V→U→Prop)
    (E:Finset (Sym2 V⊕(V×U))) (D:ℕ) (hE:E⊆ordinaryHostResources Q H)
    (hD:∀w:V⊕U,(ordinaryPhysicalGraph Q H).degree w≤D):
    (∀w,(E.filter (ordinaryResourceIncident w)).card≤D) ∧
      E.card≤Fintype.card (V⊕U)*D:=by
  have hi:∀w,(E.filter (ordinaryResourceIncident w)).card≤D:=by
    intro w
    have hs:(E.filter (ordinaryResourceIncident w)).card≤(ordinaryPhysicalIncidentEdges Q H w).card:=by
      rw [←ordinaryHostResources_filter_incident]
      exact Finset.card_le_card (Finset.filter_subset_filter _ hE)
    apply hs.trans
    cases w with
    | inl v=>
      rw [ordinaryPhysicalIncidentEdges_rim_card,←ordinary_physical_degree_row]
      exact hD (Sum.inl v)
    | inr u=>
      rw [ordinaryPhysicalIncidentEdges_hub_card,←ordinary_physical_degree_column]
      exact hD (Sum.inr u)
  exact ⟨hi,ordinary_resource_count_from_incidence E D hi⟩
end Oberwolfach
