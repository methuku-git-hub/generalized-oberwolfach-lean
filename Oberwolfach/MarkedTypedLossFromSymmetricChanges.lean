module

public import Oberwolfach.MarkedReferenceCompletionTypedChangeGraphs
public import Oberwolfach.MarkedModifiedPhysicalIncidence

@[expose] public section
/-! The physical change graphs already used for joint pseudorandomness
also contain the original typed rims and spokes missing from a later host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_removed_typed_rim_from_pair_change
    (P D:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color)
    (hchange:∀ a, ¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈D.edgeFinset):
    ∀ x y,x≠y→markedRemovedPhysicalRim P π d σ τ s(x,y)→D.Adj x y :=by
  intro x y _ h
  obtain ⟨mark,a,b,hold,hnew,heq⟩:=h
  cases mark
  · have hdiff:¬(rawMarkedPairRims P π d σ (Sum.inl (a,b))↔
        rawMarkedPairRims P π d τ (Sum.inl (a,b))):=by
      simp only [rawMarkedPairRims,Sum.elim_inl]
      exact fun iff=>hnew (iff.mp hold)
    have hd:=hchange (Sum.inl (a,b)) hdiff
    simp only [markedPairPhysical,Sum.elim_inl] at hd
    simp only [Bool.false_eq_true,ite_false] at heq
    rw [←heq] at hd
    exact SimpleGraph.mem_edgeFinset.mp hd
  · have hdiff:¬(rawMarkedPairRims P π d σ (Sum.inr (a,b))↔
        rawMarkedPairRims P π d τ (Sum.inr (a,b))):=by
      simp only [rawMarkedPairRims,Sum.elim_inr]
      exact fun iff=>hnew (iff.mp hold)
    have hd:=hchange (Sum.inr (a,b)) hdiff
    simp only [markedPairPhysical,Sum.elim_inr] at hd
    simp only [ite_true] at heq
    rw [←heq] at hd
    exact SimpleGraph.mem_edgeFinset.mp hd

theorem marked_missing_spoke_from_pair_change
    (D:SimpleGraph (V⊕U)) (H H':Bool→V→U→Prop)
    (hchange:∀ b v u,¬(H b v u↔H' b v u)→D.Adj (Sum.inl v) (Sum.inr u)):
    ∀ b v u,H b v u→¬H' b v u→D.Adj (Sum.inl v) (Sum.inr u):=by
  intro b v u hold hnew
  apply hchange b v u
  exact fun iff=>hnew (iff.mp hold)
end Oberwolfach
