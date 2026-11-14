module

public import Oberwolfach.LongEveryClassSameDeletionReady

@[expose] public section
/-! The class matching witness supplies the reserved lists for its own
deleted host and its own retained sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem long_matching_reserved_lists_from_witness
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (Δ:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (T:Finset (Fin n))
    (K:ℕ) (θ D alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n))
    (hF:∀u,(F u).IsRegularOfDegree 2) (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion P π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (S Del:SimpleGraph (Fin n)) (M:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness Δ P π d r z T K θ D alpha γ eps βList F hF weight w D₀ C S M Del):
    ∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
      (rawReservedSpokeList π d (fun e=>z.1 (Sum.inr e)) u\
        (T∪retainedFinalMarkedAt π d (fun e=>z.1 (Sum.inr e))
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) (βList/2) := by
  rcases hw with ⟨_,_,_,_,_,_,_,_,_,_,_,hmatch⟩
  exact hmatch.2
end Oberwolfach
