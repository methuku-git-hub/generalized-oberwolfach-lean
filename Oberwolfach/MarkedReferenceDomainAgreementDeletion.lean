module

public import Oberwolfach.MarkedReferenceInputStability

@[expose] public section

/-! Agreement on each original fixed domain survives physical deletion;
all roots remain ambient and the realised deletion loss is charged once. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem marked_spoke_reference_change_after_deletion_on_fixed_domains
    (π : Equiv.Perm V) (d : ℕ) (σ : RawMarkedOutcome V U Γ Color)
    (g : Γ) (j : Color) (H : Bool→V→U→Prop)
    (DR : SimpleGraph V) (DS : SimpleGraph (V⊕U)) (A:Finset V) (B:Finset U) (eR eC δ : ℝ)
    (hrow : ∀ b x,(∑ u∈B,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤eR)
    (hcol : ∀ b u,(∑ x∈A,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)≤eC)
    (hDS : ∀ z,(DS.degree z:ℝ)≤δ) :
    (∀ b x,(∑ u∈B,if ¬(rawMarkedPairSpokes π d (rawMarkedDeleteRims σ DR.edgeFinset) g j b x u↔
      markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0)≤eR+δ) ∧
    (∀ b u,(∑ x∈A,if ¬(rawMarkedPairSpokes π d (rawMarkedDeleteRims σ DR.edgeFinset) g j b x u↔
      markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0)≤eC+δ) := by
  have tri (a b c : Prop) : (if ¬(a↔c) then (1:ℝ) else 0)≤
      (if ¬(a↔b) then (1:ℝ) else 0)+(if ¬(b↔c) then (1:ℝ) else 0) := by
    by_cases ha:a <;> by_cases hb:b <;> by_cases hc:c <;> simp [ha,hb,hc]
  constructor
  · intro b x
    have hchange := (marked_spoke_physical_deletion_row_change H DS B b x).trans (hDS (Sum.inl x))
    calc
      _ ≤ (∑ u∈B,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)+
          (∑ u∈B,if ¬(H b x u↔markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0) := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro u _
        exact tri (rawMarkedPairSpokes π d σ g j b x u) (H b x u) (markedDeletePhysicalSpokes H DS b x u)
      _ ≤ eR+δ := add_le_add (hrow b x) hchange
  · intro b u
    have hchange := (marked_spoke_physical_deletion_column_change H DS A b u).trans (hDS (Sum.inr u))
    calc
      _ ≤ (∑ x∈A,if ¬(rawMarkedPairSpokes π d σ g j b x u↔H b x u) then (1:ℝ) else 0)+
          (∑ x∈A,if ¬(H b x u↔markedDeletePhysicalSpokes H DS b x u) then (1:ℝ) else 0) := by
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro x _
        exact tri (rawMarkedPairSpokes π d σ g j b x u) (H b x u) (markedDeletePhysicalSpokes H DS b x u)
      _ ≤ eC+δ := add_le_add (hcol b u) hchange

end Oberwolfach
