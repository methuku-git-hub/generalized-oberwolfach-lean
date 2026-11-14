module

public import Oberwolfach.LongActualMarkedDensityLower

@[expose] public section
/-! A single density lower bound chosen from the fixed parameters. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def longCommonDensityFloor (m:ℕ) (ρ₀:ℝ):ℝ:=min (1/4) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))

theorem long_assigned_actual_common_density_lower {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    let pstar:=longCommonDensityFloor m ρ₀
    0<pstar ∧ (∀u,pstar≤longAssignedApproxOrdinaryWeight F hF K m θ u) ∧
      pstar≤(∑u,longAssignedApproxOrdinaryWeight F hF K m θ u)/D ∧
      pstar≤(∑u,longAssignedApproxMarkedWeight F hF K m θ u)/D :=by
  intro pstar
  have hO:=long_assigned_actual_ordinary_density_lower hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  have hM:=long_assigned_actual_marked_density_lower hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  have hpstar:0<pstar:=by dsimp [pstar,longCommonDensityFloor];positivity
  refine ⟨hpstar,?_,?_,?_⟩
  · intro u
    exact (min_le_left _ _).trans (hO.1 u)
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans hO.2
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans hM
end Oberwolfach
