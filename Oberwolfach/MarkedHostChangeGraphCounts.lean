module

public import Oberwolfach.MarkedReferenceCompletionHostChanges
public import Oberwolfach.PhysicalSpokeDeletion

@[expose] public section
/-! Bounds for the actual changed rim and spoke counts from physical
change graphs. No sampling density is applied to the realized changes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rim_host_change_count
    (P D:SimpleGraph V) (σ τ:RawMarkedOutcome V U Γ Color)
    (hchange:∀ x y,P.Adj x y→σ (Sum.inl s(x,y))≠τ (Sum.inl s(x,y))→D.Adj x y) (x:V):
    (Finset.univ.filter (fun y=>P.Adj x y∧σ (Sum.inl s(x,y))≠τ (Sum.inl s(x,y)))).card≤D.degree x:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hy
  simpa only [SimpleGraph.mem_neighborFinset] using hchange x y hy.1 hy.2

theorem marked_spoke_host_change_counts
    (D:SimpleGraph (V⊕U)) (H H':Bool→V→U→Prop)
    (hchange:∀ b v u,H b v u→¬H' b v u→D.Adj (Sum.inl v) (Sum.inr u)):
    (∀ v,(Finset.univ.filter (fun u=>∃ b,H b v u∧¬H' b v u)).card≤D.degree (Sum.inl v)) ∧
    (∀ u,(Finset.univ.filter (fun v=>∃ b,H b v u∧¬H' b v u)).card≤D.degree (Sum.inr u)) :=by
  constructor
  · intro v
    calc
      _ ≤ (Finset.univ.filter (fun u=>D.Adj (Sum.inl v) (Sum.inr u))).card:=by
        apply Finset.card_le_card
        intro u hu
        obtain ⟨b,hb,hn⟩:=(Finset.mem_filter.mp hu).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hchange b v u hb hn⟩
      _ ≤ _:=physical_spoke_deleted_row D v
  · intro u
    calc
      _ ≤ (Finset.univ.filter (fun v=>D.Adj (Sum.inl v) (Sum.inr u))).card:=by
        apply Finset.card_le_card
        intro v hv
        obtain ⟨b,hb,hn⟩:=(Finset.mem_filter.mp hv).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hchange b v u hb hn⟩
      _ ≤ _:=physical_spoke_deleted_col D u
end Oberwolfach
