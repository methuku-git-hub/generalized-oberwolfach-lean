module

public import Oberwolfach.OrdinaryUncoveredTargetsWithSampleBounds

@[expose] public section

/-! The only ordinary labels charged to capacity are those not in the
actual old image; their global row bound controls their local contribution. -/
set_option autoImplicit false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryUnusedTrueSpokes {V U:Type} [Fintype V] [DecidableEq V]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (Old:U→Finset V) (w:U):Finset V:=
  Finset.univ.filter (fun v=>rawIntervalFamilyState π d σ (v,w)=some (Sum.inr true) ∧ v∉Old w)

theorem ordinary_uncovered_targets_from_unmatched_rows
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (Inner:Finset V) (Hubs:Finset U) (Old:U→Finset V)
    (hno:∀w x,¬rawIntervalColouredStart π d (fun e=>σ (w,e)) x false)
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈Old w)
    (q s:U→Bool→ℝ) (θ error:ℝ)
    (hslack:∀w,1-(∑g,q w g)-(∑j,s w j)≤2*θ)
    (hlocal:∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d σ w Inner-
      (Inner.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))
    (hrow:∀w∈Hubs,((ordinaryUnusedTrueSpokes π d σ Old w).card:ℝ)≤error):
    ∀w∈Hubs,(((ordinaryInnerSpokeTargets Inner Hubs
      (fun v u=>v∈rawReservedSpokeList π d σ u) w)\Old w).card:ℝ)≤
      2*θ*Inner.card+(Inner.card:ℝ)^(3/4:ℝ)+error :=by
  apply ordinary_uncovered_targets_with_sample_bounds π d σ Inner Hubs Old
    (ordinaryUnusedTrueSpokes π d σ Old) hno happrox ?_ q s θ error hslack hlocal ?_
  · intro w x hx
    by_cases ho:x∈Old w
    · exact Or.inl ho
    · right
      simp [ordinaryUnusedTrueSpokes,hx,ho]
  · intro w hw
    have hh:((ordinaryUnusedTrueSpokes π d σ Old w∩Inner).card:ℝ)≤
        (ordinaryUnusedTrueSpokes π d σ Old w).card:=by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    exact hh.trans (hrow w hw)
end Oberwolfach
