module

public import Oberwolfach.LongActualMarkedDensityLower

@[expose] public section
/-! The prescribed long-class sampling recipe supplies the positive and
upper coefficient bounds required by the matching construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_actual_matching_coefficients {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    (∀u,(1/4:ℝ)≤longAssignedApproxOrdinaryWeight F hF K m θ u ∧
      longAssignedApproxOrdinaryWeight F hF K m θ u≤1) ∧
    0<(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D ∧
    0<(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D :=by
  have hh:=long_assigned_factor_family_actual_marginals hn F hF Allowed hAllowed K hK m d hm hd θ ρ D
    hθ0 hθ (hρ₀.trans_le hρlo) hρ1 hD hsize hcut hclass
  have ho:=long_assigned_actual_ordinary_density_lower hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  have hm':=long_assigned_actual_marked_density_lower hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  constructor
  · intro u
    refine ⟨ho.1 u,?_⟩
    have hb:=(hh.1 u).2.2.1
    simpa only [longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction,Finset.mem_filter,Finset.mem_univ,true_and] using hb
  · exact ⟨(by positivity : 0<ρ₀/8).trans_le ho.2,
      (by positivity : 0<ρ₀/(6*((m:ℝ)+1))).trans_le hm'⟩
end Oberwolfach
