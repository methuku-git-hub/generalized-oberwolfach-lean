module

public import Oberwolfach.OrdinaryUncoveredTargetsFromUnmatchedRows
public import Oberwolfach.OrdinaryLocalUncoveredTargetBudget
public import Oberwolfach.OrdinaryInnerTargetFluctuationEventually

@[expose] public section

/-! Given the actual occupancy and matching row estimates, a contraction
chosen before θ suffices for every hub's uncovered target set. -/
set_option autoImplicit false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_targets_fit_placement_eventually
    (ε c θ z a γ:ℝ) (hθ:0≤θ) (hz:0<z) (hε:ε≤c/16) (hzfloor:c*θ≤z)
    (ha:a≤z/16) (hγ:γ≤z/16):
    ∃N:ℕ,∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (Inner:Finset (Fin n)) (Hubs:Finset U) (Old:U→Finset (Fin n)) (q s:U→Bool→ℝ),
    (Inner.card:ℝ)≤ε*n→
    (∀w x,¬rawIntervalColouredStart π d (fun e=>σ (w,e)) x false)→
    (∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈Old w)→
    (∀w,1-(∑g,q w g)-(∑j,s w j)≤2*θ)→
    (∀w∈Hubs,|rawIntervalUnassignedHubCountOn π d σ w Inner-
      (Inner.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Inner.card:ℝ)^(3/4:ℝ))→
    (∀w∈Hubs,((ordinaryUnusedTrueSpokes π d σ Old w).card:ℝ)≤(max a γ)*n)→
    ∀w,(((ordinaryInnerSpokeTargets Inner Hubs
      (fun v u=>v∈rawReservedSpokeList π d σ u) w)\Old w).card:ℝ)≤z*n :=by
  obtain ⟨N,hN⟩:=ordinary_inner_target_fluctuation_eventually z hz
  refine ⟨N,?_⟩
  intro n hn U _ _ π d σ Inner Hubs Old q s hInner hno happrox hslack hlocal hrow w
  have hn0:(0:ℝ)≤n:=by positivity
  have hmax:max a γ≤z/16:=max_le ha hγ
  have herr:(max a γ)*n≤z*n/16:=by
    have hh:=mul_le_mul_of_nonneg_right hmax hn0
    linarith
  have hfluct:=hN n hn Inner
  have hbudget:=ordinary_local_uncovered_target_budget (n:ℝ) Inner.card ε c θ z ((max a γ)*n)
    ((Inner.card:ℝ)^(3/4:ℝ)) hn0 hθ hz.le hε hzfloor hInner herr hfluct
  by_cases hw:w∈Hubs
  · exact (ordinary_uncovered_targets_from_unmatched_rows π d σ Inner Hubs Old hno happrox q s θ
      ((max a γ)*n) hslack hlocal hrow w hw).trans hbudget
  · have hzn:0≤z*n:=mul_nonneg hz.le hn0
    simpa [ordinaryInnerSpokeTargets,hw] using hzn
end Oberwolfach
