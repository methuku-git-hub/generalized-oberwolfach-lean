module

public import Oberwolfach.MarkedEndpointPairingWitness

@[expose] public section

/-! Endpoint bijections selected away from a physical deletion remain
valid in the graph after deletion, with the same types and pairings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem marked_endpoint_physical_restriction
    (A₀ A₁ X₀ X₁:Finset V) (Y₀ Y₁:Finset U) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (b:ℕ)
    (P:MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b)
    (D:SimpleGraph (V⊕U)) (hPD:Disjoint P.graph D):
    ∃ P':MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁
      (fun v u=>H₀ v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
      (fun v u=>HK v u∧¬D.Adj (Sum.inl v) (Sum.inr u)) π b,
      P'.incoming=P.incoming∧P'.outgoing=P.outgoing∧P'.graph=P.graph:=by
  have ha (a:A₀⊕A₁):¬D.Adj (Sum.inl (taggedSubsetValue A₀ A₁ a))
      (Sum.inr (taggedSubsetValue Y₀ Y₁ (P.incoming a))):=by
    apply disjoint_graphs_no_common_edge _ _ hPD
    change ∃ y,taggedHubEmbedding Y₀ Y₁ P.hubs_disjoint y=taggedSubsetValue Y₀ Y₁ (P.incoming a)∧_
    exact ⟨P.incoming a,rfl,Or.inl (congrArg (taggedSubsetValue A₀ A₁) (P.incoming.symm_apply_apply a))⟩
  have hx (x:X₀⊕X₁):¬D.Adj (Sum.inl (taggedSubsetValue X₀ X₁ x))
      (Sum.inr (taggedSubsetValue Y₀ Y₁ (P.outgoing x))):=by
    apply disjoint_graphs_no_common_edge _ _ hPD
    change ∃ y,taggedHubEmbedding Y₀ Y₁ P.hubs_disjoint y=taggedSubsetValue Y₀ Y₁ (P.outgoing x)∧_
    exact ⟨P.outgoing x,rfl,Or.inr (congrArg (taggedSubsetValue X₀ X₁) (P.outgoing.symm_apply_apply x))⟩
  let P':MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁
      (fun v u=>H₀ v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
      (fun v u=>HK v u∧¬D.Adj (Sum.inl v) (Sum.inr u)) π b:=
    { hubs_disjoint:=P.hubs_disjoint
      incoming:=P.incoming
      outgoing:=P.outgoing
      incoming_adj:=by
        intro a
        exact ⟨(P.incoming_adj a).1,(P.incoming_adj a).2,ha a⟩
      outgoing_adj:=by
        intro x
        have hh:=P.outgoing_adj x
        unfold markedOutgoingAssignment at hh ⊢
        split_ifs at hh ⊢ <;> exact ⟨hh.1,hh.2,hx x⟩
      separated:=P.separated }
  exact ⟨P',rfl,rfl,rfl⟩

end Oberwolfach
