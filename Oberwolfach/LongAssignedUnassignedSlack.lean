module

public import Oberwolfach.LongAssignedSamplingRecipe
public import Oberwolfach.LongPreparationVertexFractions

@[expose] public section
/-! The original long-class sampling recipe leaves at least theta of each
hub's vertices unassigned; no additional sampling assumption is used. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_unassigned_probability_at_least_theta
    {n:ℕ} {U:Type} [Fintype U] (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (hm:0<m) (θ:ℝ) (hθ:θ≤1) (u:U):
    θ≤1-(∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)-
      (∑j:Bool,longAssignedSpokeProbability F hF K m θ u j):=by
  let f:=ordinaryAssignedFraction F hF K u
  have hf:∀j,0≤f j:=by
    intro j
    dsimp [f,ordinaryAssignedFraction]
    positivity
  have hpart:f none+∑i:Fin K,f (some i)=1:=by
    have hh:=long_preparation_vertex_fractions (V:=Fin n) (by simpa using hn) K
      (longPreparationCycleClass (F u) (hF u) K)
    simpa [f,ordinaryAssignedFraction] using hh.2
  have hkeep:(∑i:Fin K,if θ/(100*(K:ℝ))≤f (some i) then f (some i) else 0)≤∑i:Fin K,f (some i):=by
    apply Finset.sum_le_sum
    intro i hi
    split_ifs <;> simp [hf]
  have hmult:=mul_le_mul_of_nonneg_left hkeep (show 0≤1-θ by linarith)
  have hm0:(m:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hm)
  have hsum: (∑g:Bool,longAssignedIntervalProbability F hF K m θ u g)+
      (∑j:Bool,longAssignedSpokeProbability F hF K m θ u j)=
      (1-θ)*(f none+(∑i:Fin K,if θ/(100*(K:ℝ))≤f (some i) then f (some i) else 0)):=by
    dsimp only [f]
    simp only [Fintype.sum_bool, longAssignedIntervalProbability,longAssignedSpokeProbability,
      longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight, Bool.false_eq_true, if_false, if_true]
    have hmp:(m:ℝ)+1≠0:=by positivity
    field_simp [hm0,hmp]
    ring
  nlinarith [hmult]
end Oberwolfach
