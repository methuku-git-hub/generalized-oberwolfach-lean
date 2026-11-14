module

public import Oberwolfach.MarkedRawStateChange

@[expose] public section
/-! Diagonal coordinates and physical pairs outside the fixed graph cannot
change a typed rim state, regardless of their raw categorical states. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_rim_change_of_raw_state_on_host
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V)
    (hstate:∀ e,e∈P.edgeFinset→σ (Sum.inl e)≠τ (Sum.inl e)→e∈D.edgeFinset):
    ∀ a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈D.edgeFinset:=by
  intro a h
  by_contra hd
  by_cases hp:markedPairPhysical π a∈P.edgeFinset
  · have heq:σ (Sum.inl (markedPairPhysical π a))=τ (Sum.inl (markedPairPhysical π a)):=by
      by_contra hn
      exact hd (hstate _ hp hn)
    cases a with
    | inl xy=>
      simp only [markedPairPhysical,Sum.elim_inl] at heq
      simp only [rawMarkedPairRims,Sum.elim_inl,markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation] at h
      simp [heq] at h
    | inr xy=>
      simp only [markedPairPhysical,Sum.elim_inr] at heq
      simp only [rawMarkedPairRims,Sum.elim_inr,markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation] at h
      simp [heq] at h
  · cases a with
    | inl xy=>
      have hn:¬P.Adj xy.1 xy.2:=by simpa [markedPairPhysical] using hp
      simp only [rawMarkedPairRims,Sum.elim_inl,markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation] at h
      simp [hn] at h
    | inr xy=>
      have hn:¬P.Adj xy.1 (π xy.2):=by simpa [markedPairPhysical] using hp
      simp only [rawMarkedPairRims,Sum.elim_inr,markedPhysicalRim,permutationSeparatedMatrix,markedPhysicalOrientation] at h
      simp [hn] at h
end Oberwolfach
