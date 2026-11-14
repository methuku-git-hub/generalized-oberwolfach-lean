module

public import Oberwolfach.OrdinaryUncoveredInnerTargetsFromLocalStates

@[expose] public section

/-! Local unassigned-state concentration and the matching's unused spokes
bound the actual uncovered targets at each hub. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uncovered_targets_with_sample_bounds
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (Inner:Finset V) (Hubs:Finset U) (Old Unused:U→Finset V)
    (hno:∀w x,¬rawIntervalColouredStart π d (fun e=>σ (w,e)) x false)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈Old w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈Old w ∨ x∈Unused w)
    (q s:U→Bool→ℝ) (θ error:ℝ)
    (hslack:∀w,1-(∑g,q w g)-(∑j,s w j)≤2*θ)
    (hlocal:∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d σ w Inner-
      (Inner.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))
    (hunused:∀w∈Hubs,((Unused w∩Inner).card:ℝ)≤error):
    ∀w∈Hubs,(((ordinaryInnerSpokeTargets Inner Hubs
      (fun v u=>v∈rawReservedSpokeList π d σ u) w)\Old w).card:ℝ)≤
      2*θ*Inner.card+(Inner.card:ℝ)^(3/4:ℝ)+error :=by
  intro w hw
  have ht:=ordinary_uncovered_inner_targets_from_local_states π d σ Inner Hubs Old Unused hno happrox hordinary w
  have hmean:=mul_le_mul_of_nonneg_left (hslack w) (show (0:ℝ)≤Inner.card by positivity)
  have hdev:rawIntervalUnassignedHubCountOn π d σ w Inner-
      (Inner.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))<(Inner.card:ℝ)^(3/4:ℝ):=
    (abs_lt.mp (hlocal w hw)).2
  nlinarith [hunused w hw]
end Oberwolfach
