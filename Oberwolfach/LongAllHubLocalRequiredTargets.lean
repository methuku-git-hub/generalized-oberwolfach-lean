module

public import Oberwolfach.LongInnerRequiredTargetLocal

@[expose] public section
/-! Specialize the local required-target estimate to every hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_all_hub_local_required_targets
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m d:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (π:Equiv.Perm (Fin n))
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (A:Finset (Fin n)) (occupied unused:U→Finset (Fin n))
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈occupied w ∨ x∈unused w)
    (ζ:ℝ) (hrows:RetainedRestrictionLocalGood π d σ false t A Finset.univ ζ J)
    (hfixed:∀w,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ)):
    ∀w,((A\(rawReservedSpokeList π d σ w∪retainedFinalMarkedAt π d σ t J w∪occupied w)).card:ℝ)≤
      2*θ*A.card+(A.card:ℝ)^(3/4:ℝ)+ζ*A.card+((unused w∩A).card:ℝ) :=by
  intro w
  have hh:=long_inner_required_targets_local_bound hn hK m d hm F hF θ hθ hθ1 π σ t J
    Finset.univ A (fun _=>∅) occupied unused happrox hordinary ζ hrows (by intro u _;exact hfixed u) w (Finset.mem_univ _)
  simpa only [innerRequiredTargets,Finset.mem_univ,if_true,Finset.union_empty] using hh
end Oberwolfach
