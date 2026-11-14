module

public import Oberwolfach.LongCommonDensityLower

@[expose] public section
/-! The original long-class parameters satisfy the full density bounds
needed for uniform seed-weight constants. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_actual_density_bounds {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    let b:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p:=(∑u,b u)/D
    let k:=(∑u,a u)/D
    let pstar:=longCommonDensityFloor m ρ₀
    0<pstar ∧ pstar≤p ∧ p≤1 ∧ pstar≤k ∧ k≤1 ∧ (∀u,pstar≤b u ∧ b u≤1) :=by
  intro b a p k pstar
  have hfloor:=long_assigned_actual_common_density_lower hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  have hlaw:=long_assigned_actual_raw_law_parameters hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  have hmarg:=long_assigned_factor_family_actual_marginals hn F hF Allowed hAllowed K hK m d hm hd θ ρ D
    hθ0 hθ (hρ₀.trans_le hρlo) hρ1 hD hsize hcut hclass
  dsimp only at hfloor hlaw hmarg
  rcases hlaw with ⟨hp₁,hk₁,hp,hk,hu,hsum,hq,hQ,hs,hS⟩
  rcases hmarg with ⟨hcol,htypes,hq',hQ',hs',hS',hp',hk',hp₂,hk₂,hu',hsum',hle,hkeq⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hcol
  have hp1:p≤1:=by dsimp only [p,b] at *;linarith
  have hk1:k≤1:=by dsimp only [k,a] at *;linarith
  refine ⟨hfloor.1,hfloor.2.2.1,hp1,hfloor.2.2.2,hk1,?_⟩
  intro u
  refine ⟨hfloor.2.1 u,?_⟩
  simpa only [b,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using (hcol u).2.2.1
end Oberwolfach
