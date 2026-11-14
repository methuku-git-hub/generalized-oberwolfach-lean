module

public import Oberwolfach.LongAssignedConcreteSampling
public import Oberwolfach.LongAssignedSamplingRecipe
public import Oberwolfach.RawSeedProbabilityUpperBounds

@[expose] public section
/-! The upper seed-probability bounds follow from the actual sampling recipe. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_actual_probability_upper {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
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
    p≤1 ∧ k≤1 ∧ ∀u,b u≤1 :=by
  intro b a p k
  have h:=long_assigned_factor_concrete_sampling hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  dsimp only at h
  rcases h with ⟨hcol,hq,hQ,hs,hS,hpstar,hpstarU,ht,hts,htone,hks,hkp,hkk,hkeq,hp₁,hk₁,hp₂,hk₂,hu,hsum,hle⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hs hS hp₂ hk₂ hu hsum hle
  let q:=longAssignedIntervalProbability F hF K m θ
  let s:=longAssignedSpokeProbability F hF K m θ
  have hq':∀u j,0≤q u j:=by simpa only [q,longAssignedIntervalProbability,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hq
  have hs':∀u j,0≤s u j:=by simpa only [s,longAssignedSpokeProbability,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hs
  have hS':∀u,∑j,s u j≤ intervalUncoveredProbability d (∑j,q u j):=by
    simpa only [s,q,longAssignedSpokeProbability,longAssignedIntervalProbability,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hS
  have hp0:0≤p:=by
    dsimp only [p,b,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction]
    linarith [hp₂]
  have hk0:0≤k:=by
    dsimp only [k,a,longAssignedApproxMarkedWeight,ordinaryAssignedFraction]
    have hρpos:0≤ρ₀/(6*((m:ℝ)+1)):=by positivity
    linarith only [hk₂,hρpos]
  have hpk:2*p+2*k≤1:=by
    dsimp only [p,k,b,a,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction]
    linarith only [hle,hp₁,hk₁,hu]
  have hh:=raw_seed_probability_upper_bounds d p k hp0 hk0 hpk q hq' s hs' hS'
  exact ⟨hh.1,hh.2.1,fun u=>by simpa [s,longAssignedSpokeProbability] using hh.2.2 u true⟩
end Oberwolfach
