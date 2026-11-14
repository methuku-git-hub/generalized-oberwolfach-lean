module

public import Oberwolfach.LongAssignedUniformSeedCoefficients
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! The preparation hierarchy yields fixed lower bounds for the actual
ordinary-spoke and approximate rim densities before the input factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_actual_uniform_seed_density {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
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
    let pstar:=min (1/4:ℝ) (min (ρ₀/8) (ρ₀/(6*((m:ℝ)+1))))
    0<pstar ∧ pstar≤p ∧ pstar≤k ∧ ∀u,pstar≤b u :=by
  intro b a p k pstar
  have h:=long_assigned_uniform_family_seed_coefficients hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  dsimp only at h
  have heqA:∀u,(1-θ)*(((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none)).card:ℝ)/n)/((m:ℝ)+1)-(1/100)/(m:ℝ)=a u:=by
    intro u
    rfl
  have heqB:∀u,(m:ℝ)*((1-θ)*(((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=none)).card:ℝ)/n)/((m:ℝ)+1)-(1/100)/(m:ℝ))+
      (1-θ)*∑i:Fin K,(if θ/(100*(K:ℝ))≤(((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n)
        then (((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i)).card:ℝ)/n) else 0)=b u:=by
    intro u
    rfl
  rcases h with ⟨hpos,hp,hk,hb,_⟩
  refine ⟨hpos,?_,?_,?_⟩
  · dsimp only [p]
    simpa only [heqB] using hp
  · dsimp only [k]
    simpa only [heqA] using hk
  · intro u
    simpa only [heqB u] using hb u
end Oberwolfach
