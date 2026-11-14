module

public import Oberwolfach.RetainedRawIntervalRootUpperGeneral
public import Oberwolfach.LongAssignedIntervalSumBounds

@[expose] public section
/-! The original start-count tests bound the number of retained and
approximate intervals at any one hub. -/
set_option autoImplicit false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_root_count_upper
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (m d:ℕ) (hm:0<m) (hd:0<d)
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
    (π:Equiv.Perm (Fin n)) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ)):
    (Fintype.card (retainedAndRawIntervalIndex π d σ false true t Jret w):ℝ)≤
      ((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ):=by
  let c:ℝ:=(m:ℝ)+1
  have hc:0<c:=by dsimp [c];positivity
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hnR:0≤(n:ℝ):=by positivity
  have hq:=long_assigned_interval_probability_sum_le (K:=K) hn m hm F hF θ hθ hθ1 w
  simp only [Fintype.sum_bool] at hq
  have hqc:c*(longAssignedIntervalProbability F hF K m θ w false+
      longAssignedIntervalProbability F hF K m θ w true)≤1:=by
    dsimp [c] at *
    apply (le_div_iff₀ (by positivity:(0:ℝ)<(m:ℝ)+1)).mp at hq
    nlinarith
  have hroot:=retained_raw_interval_root_upper_general π d (m+1) hd (by omega) σ t Jret w
    (longAssignedIntervalProbability F hF K m θ w) ((n:ℝ)^(3/4:ℝ)) hcounts
  push_cast at hroot
  change c*(d:ℝ)*_≤(n:ℝ)*(c*_)+2*c*_ at hroot
  have hmul:=mul_le_mul_of_nonneg_left hqc hnR
  have hc1:1≤c:=by
    dsimp [c]
    have hm0:(0:ℝ)≤m:=by positivity
    linarith
  have hnC:(n:ℝ)≤c*n:=by nlinarith [mul_nonneg (sub_nonneg.mpr hc1) hnR]
  have hscaled:c*((d:ℝ)*(Fintype.card (retainedAndRawIntervalIndex π d σ false true t Jret w):ℝ))≤
      c*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ)):=by
    calc
      _ = c*(d:ℝ)*(Fintype.card (retainedAndRawIntervalIndex π d σ false true t Jret w):ℝ):=by ring
      _ ≤ (n:ℝ)*(c*(longAssignedIntervalProbability F hF K m θ w false+
          longAssignedIntervalProbability F hF K m θ w true))+2*c*(n:ℝ)^(3/4:ℝ):=hroot
      _ ≤ (n:ℝ)+2*c*(n:ℝ)^(3/4:ℝ):=by linarith
      _ ≤ c*(n:ℝ)+2*c*(n:ℝ)^(3/4:ℝ):=by linarith
      _ = _ :=by ring
  have hbound:((d:ℝ)*(Fintype.card (retainedAndRawIntervalIndex π d σ false true t Jret w):ℝ))≤
      (n:ℝ)+2*(n:ℝ)^(3/4:ℝ):=le_of_mul_le_mul_left hscaled hc
  apply (le_div_iff₀ hdR).2
  nlinarith
end Oberwolfach
