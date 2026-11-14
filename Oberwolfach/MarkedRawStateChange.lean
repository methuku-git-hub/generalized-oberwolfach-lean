module

public import Oberwolfach.MarkedModifiedPhysicalIncidence

@[expose] public section
/-! A change of a typed rim state is supported on the physical pair whose
raw state changed, including changes of direction and mark. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rim_change_of_raw_state_change
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V)
    (hstate:∀ e,σ (Sum.inl e)≠τ (Sum.inl e)→e∈D.edgeFinset):
    ∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈D.edgeFinset:=by
  intro a h
  by_contra hd
  have heq:σ (Sum.inl (markedPairPhysical π a))=τ (Sum.inl (markedPairPhysical π a)):=by
    by_contra hn
    exact hd (hstate _ hn)
  cases a with
  | inl xy=>
    simp only [markedPairPhysical,Sum.elim_inl] at heq
    simp only [rawMarkedPairRims,Sum.elim_inl,markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation] at h
    simp [heq] at h
  | inr xy=>
    simp only [markedPairPhysical,Sum.elim_inr] at heq
    simp only [rawMarkedPairRims,Sum.elim_inr,markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation] at h
    simp [heq] at h
end Oberwolfach
