module

public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! Both interval colours have marginal probability at most the reciprocal of
the path parameter, uniformly in the original factor family. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_interval_probability_upper
    {n:ℕ} {U:Type} [Fintype U] (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (hm:0<m) (θ:ℝ) (hθ:0≤θ) (u:U) (g:Bool):
    longAssignedIntervalProbability F hF K m θ u g≤1/(m:ℝ):=by
  have hnR:(0:ℝ)<n:=by exact_mod_cast hn
  have hmR:(0:ℝ)<m:=by exact_mod_cast hm
  have hfrac:ordinaryAssignedFraction F hF K u none≤1:=by
    unfold ordinaryAssignedFraction
    apply (div_le_one hnR).2
    have hc:(Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none)).card≤n:=by
      calc
        _ ≤ (Finset.univ:Finset (Fin n)).card:=Finset.card_le_card (Finset.filter_subset _ _)
        _ = n:=by simp
    exact_mod_cast hc
  have hfrac0:0≤ordinaryAssignedFraction F hF K u none:=by
    unfold ordinaryAssignedFraction
    positivity
  cases g with
  | false =>
    simp only [longAssignedIntervalProbability, Bool.false_eq_true, ↓reduceIte]
    have hi:0≤(m:ℝ)⁻¹:=by positivity
    calc
      _ = (1/100:ℝ)*(m:ℝ)⁻¹:=by rw [div_eq_mul_inv]
      _ ≤ 1*(m:ℝ)⁻¹:=mul_le_mul_of_nonneg_right (by norm_num) hi
      _ = _:=by simp [div_eq_mul_inv]
  | true =>
    simp only [longAssignedIntervalProbability, ↓reduceIte, longAssignedApproxMarkedWeight]
    have hmul:(1-θ)*ordinaryAssignedFraction F hF K u none≤ordinaryAssignedFraction F hF K u none:=by nlinarith
    have hh:(1-θ)*ordinaryAssignedFraction F hF K u none/((m:ℝ)+1)≤1/(m:ℝ):=by
      calc
        _ ≤ ordinaryAssignedFraction F hF K u none/((m:ℝ)+1):=div_le_div_of_nonneg_right hmul (by positivity)
        _ ≤ 1/((m:ℝ)+1):=div_le_div_of_nonneg_right hfrac (by positivity)
        _ ≤ 1/(m:ℝ):=one_div_le_one_div_of_le hmR (by linarith)
    have hi:0≤(1/100:ℝ)/(m:ℝ):=by positivity
    linarith
end Oberwolfach
