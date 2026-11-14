module

public import Oberwolfach.LongAssignedTotalSamplingMass

@[expose] public section
/-! The original long-class law leaves at most 2θ unassigned at a hub. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_unassigned_probability_at_most_two_theta
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (u:U):
    1-(∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)-
      (∑j:Bool,longAssignedSpokeProbability F hF K m θ u j)≤2*θ:=by
  have hmass:=long_assigned_sampling_mass_lower hn hK m hm F hF θ hθ hθ1 u
  have hm0:(m:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hm)
  have heq:(∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)+
      (∑j:Bool,longAssignedSpokeProbability F hF K m θ u j)=
      ((m:ℝ)+1)*(∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)+
        (1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u):=by
    simp only [Fintype.sum_bool,longAssignedIntervalProbability,longAssignedSpokeProbability,
      longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,longAssignedKeptFraction,
      Bool.false_eq_true,↓reduceIte]
    field_simp
    ring
  linarith
end Oberwolfach
