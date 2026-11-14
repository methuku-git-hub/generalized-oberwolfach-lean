module

public import Oberwolfach.MarkedTypedLossFromSymmetricChanges
public import Oberwolfach.MarkedSampleDeletedArcs

@[expose] public section
/-! Removing the shared change graphs leaves a typed subhost of the later
sample, even when the later sample has additions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_shared_change_subhost
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ τ:RawMarkedOutcome V U Γ Color) (H H':Bool→V→U→Prop)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hchange:∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→
      markedPairPhysical π a∈FR.edgeFinset)
    (hspchange:∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u)):
    (∀mark x y,markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ FR.edgeFinset (Sum.inl e)) mark x y=1→
      markedPhysicalRim P π (3*d) (fun e=>τ (Sum.inl e)) mark x y=1) ∧
    (∀b v u,markedDeletePhysicalSpokes H FS b v u→H' b v u):=by
  constructor
  · intro mark x y hold
    have hdel:markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ∧
        s(x,if mark then π y else y)∉FR.edgeFinset:=
      (markedPhysicalRim_delete_iff P π d σ FR.edgeFinset mark x y).mp hold
    by_contra hn
    cases mark
    · have hc:=hchange (Sum.inl (x,y)) (by
        simp only [rawMarkedPairRims,Sum.elim_inl]
        exact fun iff=>hn (iff.mp hdel.1))
      simp only [markedPairPhysical,Sum.elim_inl] at hc
      exact hdel.2 (by simpa using hc)
    · have hc:=hchange (Sum.inr (x,y)) (by
        simp only [rawMarkedPairRims,Sum.elim_inr]
        exact fun iff=>hn (iff.mp hdel.1))
      simp only [markedPairPhysical,Sum.elim_inr] at hc
      exact hdel.2 (by simpa using hc)
  · intro b v u h
    change H b v u ∧ ¬FS.Adj (Sum.inl v) (Sum.inr u) at h
    by_contra hn
    exact h.2 (hspchange b v u (fun iff=>hn (iff.mp h.1)))
end Oberwolfach
