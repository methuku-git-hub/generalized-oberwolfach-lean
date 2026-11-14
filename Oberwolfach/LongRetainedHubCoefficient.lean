module

public import Oberwolfach.LongAllHubSeedCoefficients

@[expose] public section
/-! A retained frequency at a hub gives a fixed positive lower bound for
its ordinary seed coefficient, uniformly over the factor family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

theorem long_retained_hub_coefficient_lower
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (hK:0<K) (θ:ℝ) (hθ:0<θ) (hθhi:θ≤1/2)
    (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u ∧
      longAssignedApproxOrdinaryWeight F hF K m θ u≤1)
    (i:Fin K) (u:U)
    (hf:θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u):
    θ/(200*(K:ℝ))≤longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u:=by
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  have hf0:0≤longAssignedKeptFraction F hF K θ i u:=by
    have hh:0≤θ/(100*(K:ℝ)):=by positivity
    exact hh.trans hf
  have hθ':(1/2:ℝ)≤1-θ:=by linarith
  have hnum:θ/(200*(K:ℝ))≤longAssignedKeptOrdinaryContribution F hF K θ i u:=by
    rw [long_assigned_kept_fraction_contribution]
    have h:=mul_le_mul hf hθ' (by norm_num:(0:ℝ)≤1/2) hf0
    have heq:(θ/(100*(K:ℝ)))*(1/2)=θ/(200*(K:ℝ)):=by ring
    rw [heq] at h
    nlinarith
  have hnum0:0≤longAssignedKeptOrdinaryContribution F hF K θ i u:=by
    have h:0≤θ/(200*(K:ℝ)):=by positivity
    exact h.trans hnum
  have hdiv:longAssignedKeptOrdinaryContribution F hF K θ i u≤
      longAssignedKeptOrdinaryContribution F hF K θ i u/
        longAssignedApproxOrdinaryWeight F hF K m θ u:=
    le_div_self hnum0 (hb u).1 (hb u).2
  exact hnum.trans hdiv
end Oberwolfach
