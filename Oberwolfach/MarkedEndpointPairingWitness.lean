module

public import Oberwolfach.MarkedEndpointSpokeGraph
public import Oberwolfach.TaggedSubsetEmbedding
public import Oberwolfach.MarkedTypedEndpointPairing

@[expose] public section

/-! Retain the actual two bijections, their spoke types and their physical
spoke graph. The graph has maximum degree four, with no injective-label
assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def taggedHubEmbedding (Y₀ Y₁ : Finset U) (hY : Disjoint Y₀ Y₁) : Y₀⊕Y₁↪U :=
  taggedSubsetEmbedding Y₀ Y₁ hY

structure MarkedEndpointPairing
    (A₀ A₁ X₀ X₁ : Finset V) (Y₀ Y₁ : Finset U)
    (H₀ HK : V→U→Prop) (π : Equiv.Perm V) (b : ℕ) where
  hubs_disjoint : Disjoint Y₀ Y₁
  incoming : A₀⊕A₁ ≃ Y₀⊕Y₁
  outgoing : X₀⊕X₁ ≃ Y₀⊕Y₁
  incoming_adj : ∀ a,markedIncomingAssignment A₀ A₁ Y₀ Y₁ H₀ a (incoming a)
  outgoing_adj : ∀ x,markedOutgoingAssignment X₀ X₁ Y₀ Y₁ H₀ HK x (outgoing x)
  separated : ∀ y,¬PermutationClose π b
    (taggedSubsetValue A₀ A₁ (incoming.symm y)) (taggedSubsetValue X₀ X₁ (outgoing.symm y))

namespace MarkedEndpointPairing
variable {A₀ A₁ X₀ X₁ : Finset V} {Y₀ Y₁ : Finset U}
    {H₀ HK : V→U→Prop} {π : Equiv.Perm V} {b : ℕ}

def graph (P : MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b) : SimpleGraph (V⊕U) :=
  markedEndpointSpokeGraph (fun y=>taggedSubsetValue A₀ A₁ (P.incoming.symm y))
    (fun y=>taggedSubsetValue X₀ X₁ (P.outgoing.symm y)) (taggedHubEmbedding Y₀ Y₁ P.hubs_disjoint)

theorem graph_degree (P : MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b) (z : V⊕U) :
    P.graph.degree z≤4 := by
  apply marked_endpoint_spoke_degree
  · convert label_fibre_bound_reindex _ P.incoming.symm 2 (tagged_subset_label_fibre A₀ A₁) using 1 <;> congr!
  · convert label_fibre_bound_reindex _ P.outgoing.symm 2 (tagged_subset_label_fibre X₀ X₁) using 1 <;> congr!

theorem graph_le (P : MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b) :
    P.graph≤ordinaryPhysicalGraph ⊥ (fun v u=>H₀ v u∨HK v u) := by
  apply marked_endpoint_spoke_subgraph
  · intro y
    have hh:=P.incoming_adj (P.incoming.symm y)
    rw [P.incoming.apply_symm_apply] at hh
    exact Or.inl hh.2
  · intro y
    have hh:=P.outgoing_adj (P.outgoing.symm y)
    rw [P.outgoing.apply_symm_apply] at hh
    dsimp [markedOutgoingAssignment] at hh
    split_ifs at hh with h
    · exact Or.inr hh.2
    · exact Or.inl hh.2

theorem graph_support (P : MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b) :
    GraphSupportedOn (ordinaryInnerVertices (A₀∪A₁∪(X₀∪X₁)) (Y₀∪Y₁)) P.graph := by
  apply marked_endpoint_spoke_support
  · intro y
    cases P.incoming.symm y with
    | inl a=>exact Finset.mem_union_left _ (Finset.mem_union_left _ a.property)
    | inr a=>exact Finset.mem_union_left _ (Finset.mem_union_right _ a.property)
  · intro y
    cases P.outgoing.symm y with
    | inl x=>exact Finset.mem_union_right _ (Finset.mem_union_left _ x.property)
    | inr x=>exact Finset.mem_union_right _ (Finset.mem_union_right _ x.property)
  · intro y
    cases y with
    | inl y=>exact Finset.mem_union_left _ y.property
    | inr y=>exact Finset.mem_union_right _ y.property

end MarkedEndpointPairing
end Oberwolfach
