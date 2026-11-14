module

public import Oberwolfach.LongAssignedSamplingRecipe
public import Oberwolfach.LongPreparationFactorClassification

@[expose] public section
/-! In the all-long-component case the two original interval probabilities
have total mass exactly (1-θ)/(m+1). -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_all_cycles_interval_mass
    {n:ℕ} {U:Type} [Fintype U] (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (θ:ℝ) (u:U) (hAll:∀v,K<Fintype.card ((F u).connectedComponentMk v)):
    longAssignedIntervalProbability F hF K m θ u false+
      longAssignedIntervalProbability F hF K m θ u true=(1-θ)/((m:ℝ)+1):=by
  have hnR:(n:ℝ)≠0:=by exact_mod_cast (ne_of_gt hn)
  have hc:∀v,longPreparationCycleClass (F u) (hF u) K v=none:=
    fun v=>((long_preparation_cycle_class (F u) (hF u) K v).1).2 (hAll v)
  have hf:ordinaryAssignedFraction F hF K u none=1:=by
    unfold ordinaryAssignedFraction
    simp [hc,hnR]
  simp only [longAssignedIntervalProbability,Bool.false_eq_true,↓reduceIte,longAssignedApproxMarkedWeight,hf,mul_one]
  ring
end Oberwolfach
