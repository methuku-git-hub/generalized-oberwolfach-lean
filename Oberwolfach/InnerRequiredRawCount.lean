module

public import Oberwolfach.InnerRequiredRawStateCover
public import Oberwolfach.RawIntervalUnassignedHubRestricted
public import Oberwolfach.RetentionRestrictionCommonEvent

@[expose] public section
/-! Convert the raw-state cover to the size estimate needed by the
prescribed-position capacity calculation. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem raw_unassigned_restricted_count_card
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (w:U) (vertices:Finset V):
    ((rawUnassignedAt π d σ w∩vertices).card:ℝ)=rawIntervalUnassignedHubCountOn π d σ w vertices:=by
  unfold rawUnassignedAt rawIntervalUnassignedHubCountOn
  have heq:(Finset.univ.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none))∩vertices=
      vertices.filter (fun x=>rawIntervalFamilyState π d σ (x,w)=none):=by
    ext x;simp [and_comm]
  rw [heq]
  simp [Finset.sum_ite]

theorem inner_required_targets_count_from_raw_cover
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (inner:Finset U) (vertices:Finset V) (absorber occupied unused:U→Finset V)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈occupied w ∨ x∈unused w)
    (ζ:ℝ) (hrows:RetainedRestrictionGood π d σ false t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J):
    ∀w,((innerRequiredTargets inner vertices (rawReservedSpokeList π d σ)
      (retainedFinalMarkedAt π d σ t J) absorber occupied w).card:ℝ)≤
      rawIntervalUnassignedHubCountOn π d σ w vertices+ζ*Fintype.card V+((unused w∩vertices).card:ℝ):=by
  intro w
  have hcover:=inner_required_targets_raw_cover π d σ t J inner vertices absorber occupied unused happrox hordinary w
  have hcard:=Finset.card_le_card hcover
  have h12:=Finset.card_union_le (rawUnassignedAt π d σ w∩vertices) (rawRetentionChangedAt π d σ t J w∩vertices)
  have h123:=Finset.card_union_le ((rawUnassignedAt π d σ w∩vertices)∪(rawRetentionChangedAt π d σ t J w∩vertices)) (unused w∩vertices)
  have hcNat:(rawRetentionChangedAt π d σ t J w∩vertices).card≤(rawRetentionChangedAt π d σ t J w).card:=Finset.card_le_card (Finset.inter_subset_left)
  have hc:( ((rawRetentionChangedAt π d σ t J w∩vertices).card:ℝ))≤ζ*Fintype.card V:=by
    have hh:((rawRetentionChangedAt π d σ t J w).card:ℝ)≤ζ*Fintype.card V:=by
      simpa [RetainedRestrictionGood,rawRetentionChangedAt] using ((hrows ()).1 w)
    exact (by exact_mod_cast hcNat : ((rawRetentionChangedAt π d σ t J w∩vertices).card:ℝ)≤(rawRetentionChangedAt π d σ t J w).card).trans hh
  have h12R:=show (((rawUnassignedAt π d σ w∩vertices)∪(rawRetentionChangedAt π d σ t J w∩vertices)).card:ℝ)≤
      ((rawUnassignedAt π d σ w∩vertices).card:ℝ)+((rawRetentionChangedAt π d σ t J w∩vertices).card:ℝ) by exact_mod_cast h12
  have h123R:=show ((((rawUnassignedAt π d σ w∩vertices)∪(rawRetentionChangedAt π d σ t J w∩vertices))∪(unused w∩vertices)).card:ℝ)≤
      (((rawUnassignedAt π d σ w∩vertices)∪(rawRetentionChangedAt π d σ t J w∩vertices)).card:ℝ)+((unused w∩vertices).card:ℝ) by exact_mod_cast h123
  have hcardR:=show ((innerRequiredTargets inner vertices (rawReservedSpokeList π d σ)
      (retainedFinalMarkedAt π d σ t J) absorber occupied w).card:ℝ)≤
      ((((rawUnassignedAt π d σ w∩vertices)∪(rawRetentionChangedAt π d σ t J w∩vertices))∪(unused w∩vertices)).card:ℝ) by exact_mod_cast hcard
  rw [raw_unassigned_restricted_count_card] at h12R
  linarith
end Oberwolfach
