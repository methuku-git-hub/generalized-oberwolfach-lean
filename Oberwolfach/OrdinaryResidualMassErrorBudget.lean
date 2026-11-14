module

public import Oberwolfach.OrdinaryAssignedKeptMassBound

@[expose] public section
/-! A parameter-only error budget controls the error weighted by the actual
retained short-cycle frequency. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_residual_mass_error_budget
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ:ℝ) (hrs:0≤rsv)
    (hrsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀)
    (u:U) (base matchErr err:ℝ) (hmatch:0≤matchErr)
    (hbudget:base+matchErr*n≤err*n):
    base+matchErr*n*(∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤err*n:=by
  have hkept:=ordinary_assigned_kept_mass_le_unreserved hn F hF Allowed hAllowed K hK i₀ rsv θ hrs hrsclass hclass u
  have hn0:(0:ℝ)≤n:=by positivity
  have hm0:0≤matchErr*(n:ℝ):=mul_nonneg hmatch hn0
  have hh:=mul_le_mul_of_nonneg_left (show (∑i:Fin K,ordinaryAssignedKeptFraction F hF K i₀ rsv θ u i)≤1 by linarith) hm0
  nlinarith
end Oberwolfach
