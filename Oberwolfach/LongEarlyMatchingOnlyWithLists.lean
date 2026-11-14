module

public import Oberwolfach.LongEarlyMatchingOnlyForDeletion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

theorem long_early_matching_only_with_lists
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (r K d:ℕ) (θ D alpha γ eps ζEarly βList:ℝ)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n))
    (hMatching:∀Del:SimpleGraph (Fin n),(∀x,(Del.degree x:ℝ)≤ζEarly*n)→
      LongEarlyMatchingOnlyForDeletion (r+4) K d θ D alpha γ eps (ζEarly*n) P π F hF weight w z Del)
    (hLists:∀Del:SimpleGraph (Fin n),(∀x,(Del.degree x:ℝ)≤ζEarly*n)→
      LongSampleReservedLists P π d z Del Inner (βList/2)):
    ∀Del:SimpleGraph (Fin n),(∀x,(Del.degree x:ℝ)≤ζEarly*n)→
      LongEarlyMatchingListsForDeletion r K d θ D alpha γ eps ζEarly βList P π F hF weight w z Inner Del := by
  intro Del hDel
  exact ⟨hMatching Del hDel,hLists Del hDel⟩
end Oberwolfach
