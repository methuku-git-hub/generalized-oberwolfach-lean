module

public import Oberwolfach.ReservedSpokesAvoidRetainedMarked
public import Oberwolfach.ReservedSpokeExtendingAfterExclusions

@[expose] public section
/-! Removing retained marked labels costs nothing from a reserved list,
because the two label classes are disjoint on the original sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_spoke_trimmed_without_marked_loss
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (D:V→V→Prop) (Inner:Finset V) (β lam:ℝ) (hlam:0≤lam)
    (hbudget:lam*Fintype.card V+Inner.card≤β*Fintype.card V)
    (hext:∀w,IsExtendingList D (rawReservedSpokeList π d σ w) β):
    ∀w,IsExtendingList D (rawReservedSpokeList π d σ w\
      (Inner∪retainedFinalMarkedAt π d σ t J w)) lam:=by
  intro w
  have hdis:=raw_reserved_spoke_list_disjoint_retained_marked π d σ t J w
  have heq:rawReservedSpokeList π d σ w\(Inner∪retainedFinalMarkedAt π d σ t J w)=
      rawReservedSpokeList π d σ w\(Inner∪∅):=by
    ext x
    simp only [Finset.union_empty,Finset.mem_sdiff,Finset.mem_union]
    constructor
    · intro h;exact ⟨h.1,by tauto⟩
    · intro h
      have hn: x∉retainedFinalMarkedAt π d σ t J w:=Finset.disjoint_left.mp hdis h.1
      exact ⟨h.1,by tauto⟩
  rw [heq]
  apply extending_list_after_two_exclusions D (rawReservedSpokeList π d σ w) Inner ∅ β lam hlam
  · simpa using hbudget
  · exact hext w
end Oberwolfach
