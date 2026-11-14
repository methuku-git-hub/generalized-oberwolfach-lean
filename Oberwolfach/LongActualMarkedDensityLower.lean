module

public import Oberwolfach.LongActualOrdinaryDensityLower

@[expose] public section
/-! The marked raw rim density also has a uniform positive lower bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_actual_marked_density_lower {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    ρ₀/(6*((m:ℝ)+1))≤(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D :=by
  have h:=long_assigned_factor_family_actual_marginals hn F hF Allowed hAllowed K hK m d hm hd θ ρ D
    hθ0 hθ (hρ₀.trans_le hρlo) hρ1 hD hsize hcut hclass
  dsimp only at h
  rcases h with ⟨hcol,hclassform,hq,hQ,hs,hS,hp,hk,hp₂,hk₂,hu,hsum,hle,hkeq⟩
  have hρ:ρ₀/(6*((m:ℝ)+1))≤ρ/(6*((m:ℝ)+1)):=
    div_le_div_of_nonneg_right hρlo (by positivity)
  apply le_trans hρ
  simpa only [longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hk₂
end Oberwolfach
