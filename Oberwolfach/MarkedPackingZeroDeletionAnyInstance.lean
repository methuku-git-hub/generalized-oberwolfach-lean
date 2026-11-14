module

public import Oberwolfach.MarkedPackingLoadSpokeChanges
public import Oberwolfach.MarkedEmptyPhysicalDeletion
public import Oberwolfach.GraphBottomEdgeFinsetAnyInstance

@[expose] public section
/-! The actual adaptive packing event includes its zero-deletion case. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]
theorem marked_packing_zero_deletion_any_instance
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (D p k s₀ η C:ℝ)
    (weight:(Fin (m+1)→V)→ℝ) (a:Γ) (j:Color)
    (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop)
    (h:∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
      (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
      MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j
        (Equiv.refl U) q s (η+C*δ/Fintype.card V)
        (rawMarkedDeleteRims σ DR.edgeFinset) (markedDeletePhysicalSpokes H DS)):
    MarkedPackingLoadsWithSpokes P π d m D p k s₀ weight a j (Equiv.refl U) q s η σ H := by
  have hh:=h 0 le_rfl ⊥ ⊥ (by intro x; simp) (by intro x; simp)
  simpa only [mul_zero,zero_div,add_zero,graph_bottom_edgeFinset_any_instance,rawMarkedDeleteRims_empty,markedDeletePhysicalSpokes_bottom] using hh
end Oberwolfach
