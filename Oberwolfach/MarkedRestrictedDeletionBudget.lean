module

public import Oberwolfach.MarkedPhysicalDeletionRestriction

@[expose] public section

/-! The same ambient physical deletion restricts to each fixed level, with
its degree budget rescaled by the ratio of the ambient and level orders. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z Γ Color:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder W] [DecidableEq U] [DecidableEq Z]

theorem marked_restricted_deletion_budget
    (f:W↪V) (g:Z↪U) (σ:RawMarkedOutcome V U Γ Color)
    (H:Bool→V→U→Prop) (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U))
    (ζ K:ℝ) (hζ:0≤ζ) (hK:(Fintype.card V:ℝ)≤K*Fintype.card W)
    (hr:∀ v,(DR.degree v:ℝ)≤ζ*Fintype.card V)
    (hs:∀ z,(DS.degree z:ℝ)≤ζ*Fintype.card V):
    rawMarkedRestrictPair f g (rawMarkedDeleteRims σ DR.edgeFinset)=
      rawMarkedDeleteRims (rawMarkedRestrictPair f g σ) (DR.comap f).edgeFinset ∧
    (fun b x u=>markedDeletePhysicalSpokes H DS b (f x) (g u))=
      markedDeletePhysicalSpokes (fun b x u=>H b (f x) (g u)) (DS.comap (Sum.map f g)) ∧
    (∀ x,( (DR.comap f).degree x:ℝ)≤(ζ*K)*Fintype.card W) ∧
    (∀ z,( (DS.comap (Sum.map f g)).degree z:ℝ)≤(ζ*K)*Fintype.card W) := by
  have mult:ζ*(Fintype.card V:ℝ)≤(ζ*K)*Fintype.card W := by
    nlinarith only [mul_le_mul_of_nonneg_left hK hζ]
  have hg : (Sum.map f g : W⊕Z → V⊕U).Injective := by
    intro x y hxy
    cases x <;> cases y <;> simp_all
  let fg:W⊕Z ↪ V⊕U := ⟨Sum.map f g,hg⟩
  refine ⟨rawMarkedRestrictPair_deleteRims f g σ DR,
    markedDeletePhysicalSpokes_restrict f g H DS,?_,?_⟩
  · intro x
    have hdeg:(DR.comap f).degree x≤DR.degree (f x) := by
      rw [graph_comap_degree_into_image DR f x]
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (SimpleGraph.card_neighborFinset_eq_degree _ _)
    exact (Nat.cast_le.mpr hdeg).trans ((hr (f x)).trans mult)
  · intro z
    have hdeg:(DS.comap fg).degree z≤DS.degree (fg z) := by
      rw [graph_comap_degree_into_image DS fg z]
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (SimpleGraph.card_neighborFinset_eq_degree _ _)
    exact (Nat.cast_le.mpr hdeg).trans ((hs (fg z)).trans mult)

end Oberwolfach
