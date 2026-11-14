module

public import Oberwolfach.HubTestMassMargin
public import Oberwolfach.LongAllHubSeedCoefficients

@[expose] public section
/-! A retained length at a fixed hub supplies a uniformly large matching
test, with the actual long-class coefficient and its fixed spoke marginal. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U]

theorem long_assigned_retained_hub_test_mass
    (hn:0<n) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (K m:ℕ) (hK:0<K) (θ:ℝ) (hθ0:0<θ) (hθ:θ≤1/2)
    (hb:∀u,0<longAssignedApproxOrdinaryWeight F hF K m θ u)
    (i:Fin K) (u:U)
    (hf:θ/(100*(K:ℝ))≤longAssignedKeptFraction F hF K θ i u)
    (τ err card r rmax mass:ℝ) (hτ:τ≤1/2)
    (herr:err≤(longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u)/4)
    (hcount:longAssignedApproxOrdinaryWeight F hF K m θ u*n/2≤card)
    (hr:0<r) (hrmax:r≤rmax)
    (hmass:((1-τ)*(longAssignedKeptOrdinaryContribution F hF K θ i u/
       longAssignedApproxOrdinaryWeight F hF K m θ u)-err)*card/r≤mass):
    θ*(n:ℝ)/(1600*(K:ℝ)*rmax)≤mass :=by
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  have hcoeff:0≤longAssignedKeptOrdinaryContribution F hF K θ i u/
      longAssignedApproxOrdinaryWeight F hF K m θ u:=
    (long_assigned_all_ordinary_seed_coefficients hn F hF K m θ hθ0.le (by linarith) hb i u).1
  have hbalance:=long_assigned_all_ordinary_seed_balance F hF K m θ hb i u
  have hh:=hub_test_mass_margin (n:ℝ) (longAssignedApproxOrdinaryWeight F hF K m θ u)
    (longAssignedKeptOrdinaryContribution F hF K θ i u/longAssignedApproxOrdinaryWeight F hF K m θ u)
    (longAssignedKeptFraction F hF K θ i u) (θ/(100*(K:ℝ))) θ τ err card r rmax mass
    (Nat.cast_nonneg _) (hb u) hcoeff hf (by positivity) hθ hτ herr hcount hr hrmax hbalance hmass
  convert hh using 1 <;> field_simp <;> ring
end Oberwolfach
