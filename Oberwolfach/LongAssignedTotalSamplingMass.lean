module

public import Oberwolfach.LongAssignedFractionTotal
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! The original long-interval and retained ordinary-cycle probabilities
cover all but the stated θ-fraction of a factor. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_interval_probability_sum
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (m:ℕ) (hm:0<m)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (θ:ℝ) (u:U):
    ((m:ℝ)+1)*(∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)=
      (1-θ)*ordinaryAssignedFraction F hF K u none:=by
  have hm0:(m:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hm)
  have hmp:(m:ℝ)+1≠0:=by positivity
  simp only [Fintype.sum_bool,longAssignedIntervalProbability,longAssignedApproxMarkedWeight,Bool.false_eq_true,↓reduceIte]
  field_simp
  ring

theorem long_assigned_sampling_mass_lower
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (u:U):
    1-(101/100:ℝ)*θ≤((m:ℝ)+1)*(∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)+
      (1-θ)*(∑i:Fin K,longAssignedKeptFraction F hF K θ i u):=by
  have hp:=long_assigned_retained_fraction_mass hn hK F hF θ hθ u
  have hh:=mul_le_mul_of_nonneg_left hp (show 0≤1-θ by linarith)
  rw [long_assigned_interval_probability_sum hn m hm F hF θ u]
  nlinarith [sq_nonneg θ]
end Oberwolfach
