module

public import Oberwolfach.LongAssignedTotalSamplingMass

@[expose] public section
/-! The two interval probabilities have total mass at most one block. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_interval_probability_sum_le
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n)
    (m:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (u:U):
    (∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)≤1/((m:ℝ)+1):=by
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hc:0<((m:ℝ)+1):=by positivity
  have hfrac0:0≤ordinaryAssignedFraction F hF K u none:=by unfold ordinaryAssignedFraction;positivity
  have hfrac1:ordinaryAssignedFraction F hF K u none≤1:=by
    unfold ordinaryAssignedFraction
    apply (div_le_one hnR).2
    have hh:=Finset.card_le_univ ((Finset.univ:Finset (Fin n)).filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none))
    have hh':(((Finset.univ:Finset (Fin n)).filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none)).card:ℝ)≤n:=by
      exact_mod_cast (by simpa using hh : ((Finset.univ:Finset (Fin n)).filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none)).card≤n)
    exact hh' 
  have hprod:(1-θ)*ordinaryAssignedFraction F hF K u none≤1:=by nlinarith [mul_nonneg hθ hfrac0]
  have heq:=long_assigned_interval_probability_sum (K:=K) hn m hm F hF θ u
  apply (le_div_iff₀ hc).2
  nlinarith
end Oberwolfach
