module

public import Oberwolfach.InnerRequiredRawCount
public import Oberwolfach.RawIntervalUnassignedColumnCount

@[expose] public section
/-! Bound the number of inner indices prescribing a fixed physical label by
unassigned, retention-changed and unused-ordinary occurrences. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem raw_unassigned_restricted_column_card
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (v:V) (inner:Finset U):
    ((inner.filter (fun w=>v∈rawUnassignedAt π d σ w)).card:ℝ)=rawIntervalUnassignedColumnCount π d σ v inner:=by
  unfold rawIntervalUnassignedColumnCount rawUnassignedAt
  simp [Finset.sum_ite]

theorem inner_required_targets_occurrence_from_raw_cover
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (inner:Finset U) (vertices:Finset V) (absorber occupied unused:U→Finset V)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈occupied w ∨ x∈unused w)
    (ζ:ℝ) (hrows:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J):
    ∀v,(((Finset.univ:Finset U).filter (fun w=>v∈innerRequiredTargets inner vertices
      (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t J) absorber occupied w)).card:ℝ)≤
      rawIntervalUnassignedColumnCount π d σ v inner+ζ*Fintype.card U+
      (((Finset.univ:Finset U).filter (fun w=>v∈unused w)).card:ℝ):=by
  intro v
  let C:=inner.filter (fun w=>v∈rawUnassignedAt π d σ w)
  let T:=(Finset.univ:Finset U).filter (fun w=>v∈rawRetentionChangedAt π d σ t J w)
  let D:=(Finset.univ:Finset U).filter (fun w=>v∈unused w)
  have hsub:(Finset.univ.filter (fun w=>v∈innerRequiredTargets inner vertices
      (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t J) absorber occupied w))⊆(C∪T)∪D:=by
    intro w hw
    have hwZ: v∈innerRequiredTargets inner vertices (rawReservedSpokeList π d σ)
      (retainedFinalMarkedAt π d σ t J) absorber occupied w:=(Finset.mem_filter.mp hw).2
    have hi:w∈inner:=by
      by_contra h;have :=(inner_required_targets_properties inner vertices (rawReservedSpokeList π d σ)
        (retainedFinalMarkedAt π d σ t J) absorber occupied).1 w h
      rw [this] at hwZ
      exact Finset.notMem_empty _ hwZ
    have hcover:=inner_required_targets_raw_cover π d σ t J inner vertices absorber occupied unused happrox hordinary w hwZ
    simp only [Finset.mem_union,Finset.mem_inter] at hcover
    rcases hcover with (⟨ha,_⟩|⟨ht,_⟩)|⟨hu,_⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,ha⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩)
  have hcard:=Finset.card_le_card hsub
  have h12:=Finset.card_union_le C T
  have h123:=Finset.card_union_le (C∪T) D
  have hT:((T.card:ℝ))≤ζ*Fintype.card U:=by
    simpa [T,rawRetentionChangedAt,RetainedRestrictionGood] using ((hrows ()).2 v)
  have hC:((C.card:ℝ))=rawIntervalUnassignedColumnCount π d σ v inner:=by
    exact raw_unassigned_restricted_column_card π d σ v inner
  have hcardR:=show (((Finset.univ:Finset U).filter (fun w=>v∈innerRequiredTargets inner vertices
      (rawReservedSpokeList π d σ) (retainedFinalMarkedAt π d σ t J) absorber occupied w)).card:ℝ)≤(((C∪T)∪D).card:ℝ) by exact_mod_cast hcard
  have h12R:=show (((C∪T).card:ℝ))≤(C.card:ℝ)+(T.card:ℝ) by exact_mod_cast h12
  have h123R:=show ((((C∪T)∪D).card:ℝ))≤((C∪T).card:ℝ)+(D.card:ℝ) by exact_mod_cast h123
  dsimp only [D] at h123R
  linarith
end Oberwolfach
