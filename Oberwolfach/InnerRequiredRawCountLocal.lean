module

public import Oberwolfach.RetentionRestrictionLocalEvent
public import Oberwolfach.InnerRequiredRawCount
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

theorem inner_required_targets_count_from_local_raw_cover
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (inner:Finset U) (vertices:Finset V) (absorber occupied unused:U→Finset V)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈occupied w ∨ x∈unused w)
    (ζ:ℝ) (hrows:RetainedRestrictionLocalGood π d σ false t vertices inner ζ J):
    ∀w∈inner,((innerRequiredTargets inner vertices (rawReservedSpokeList π d σ)
      (retainedFinalMarkedAt π d σ t J) absorber occupied w).card:ℝ)≤
      rawIntervalUnassignedHubCountOn π d σ w vertices+ζ*vertices.card+((unused w∩vertices).card:ℝ):=by
  intro w hw
  have hcover:=inner_required_targets_raw_cover π d σ t J inner vertices absorber occupied unused happrox hordinary w
  have hcard:=Finset.card_le_card hcover
  have h12:=Finset.card_union_le (rawUnassignedAt π d σ w∩vertices) (rawRetentionChangedAt π d σ t J w∩vertices)
  have h123:=Finset.card_union_le ((rawUnassignedAt π d σ w∩vertices)∪(rawRetentionChangedAt π d σ t J w∩vertices)) (unused w∩vertices)
  have hc:((rawRetentionChangedAt π d σ t J w∩vertices).card:ℝ)≤ζ*vertices.card:=by
    have heq:rawRetentionChangedAt π d σ t J w∩vertices = vertices.filter (fun x=>retainedRawFamilyState π d σ false t J (x,w)≠rawIntervalFamilyState π d σ (x,w)):=by
      ext x
      simp only [rawRetentionChangedAt,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and,and_comm]
    rw [heq]
    apply le_trans ?_ (hrows.1 w hw)
    exact_mod_cast (Finset.card_le_card (by intro x hx; simpa only [Finset.mem_filter] using hx))
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
