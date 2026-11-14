module

public import Oberwolfach.MarkedReferenceCompletionTypedChanges
public import Oberwolfach.MarkedHostChangeGraphCounts

@[expose] public section
/-! The actual physical change graph bounds the number of original typed
rims missing in the later host, with no sampling-density factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_removed_typed_rim_count_of_change_graph
    (P D:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ τ:RawMarkedOutcome V U Γ Color)
    (hchange:∀ x y,x≠y→markedRemovedPhysicalRim P π d σ τ s(x,y)→D.Adj x y) (x:V):
    (Finset.univ.filter (fun y=>x≠y∧markedRemovedPhysicalRim P π d σ τ s(x,y))).card≤D.degree x:=by
  rw [←SimpleGraph.card_neighborFinset_eq_degree]
  apply Finset.card_le_card
  intro y hy
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hy
  simpa only [SimpleGraph.mem_neighborFinset] using hchange x y hy.1 hy.2
end Oberwolfach
