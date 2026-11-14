module

public import Oberwolfach.LongEarlyMatchingListsForDeletion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable

theorem extending_list_lower_parameter {V:Type} [Fintype V] [DecidableEq V]
    (D:V→V→Prop) (L:Finset V) (β β':ℝ) (hβ':0≤β') (hβ:β'≤β)
    (h:IsExtendingList D L β):IsExtendingList D L β' :=by
  have hh:β'*(Fintype.card V:ℝ)≤β*(Fintype.card V:ℝ):=
    mul_le_mul_of_nonneg_right hβ (Nat.cast_nonneg _)
  exact ⟨hβ',hh.trans h.2.1,fun x=>⟨hh.trans (h.2.2.1 x).1,hh.trans (h.2.2.1 x).2⟩,
    fun x y hxy=>hh.trans (h.2.2.2 x y hxy)⟩

/-- The lists supplied by the early matching event also satisfy any smaller
positive residual list threshold for the identical sample and deletion. -/
theorem long_early_lists_residual_extending
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (r d:ℕ) (θ D a γ eps Δ βList βfinal:ℝ)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle P (longPaddedSeedExponent i+2)→ℝ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Inner:Finset (Fin n))
    (hβ:0≤βfinal) (hcap:βfinal≤βList/2)
    (hEarly:∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      LongEarlyMatchingListsForDeletion r K d θ D a γ eps Δ βList P π F hF weight w z Inner Del):
    ∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤Δ*n)→
      ∀u,IsExtendingList (fun x y=>rawSelectedPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
        (rawReservedSpokeList π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e))) u \
          (Inner∪retainedFinalMarkedAt π d (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1 (Sum.inr e)))
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 u)) βfinal :=by
  intro Del hDel u
  have hLists:LongSampleReservedLists P π d z Del Inner (βList/2):=(hEarly Del hDel).2
  exact extending_list_lower_parameter _ _ _ _ hβ hcap (hLists u)
end Oberwolfach
