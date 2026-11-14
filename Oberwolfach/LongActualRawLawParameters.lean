module

public import Oberwolfach.LongAssignedConcreteSampling
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! The parameters in the actual long-class recipe define the expanded raw
law and its hub-dependent interval and spoke marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_actual_raw_law_parameters {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    let b:=longAssignedApproxOrdinaryWeight F hF K m θ
    let a:=longAssignedApproxMarkedWeight F hF K m θ
    let p₁:=ρ*(1/100)/2
    let k₁:=ρ*((1/100)/(m:ℝ))/2
    let p₂:=(∑u,b u)/D
    let k₂:=(∑u,a u)/D
    let udens:=2*(∑u,(1-1/100-(1/100)/(m:ℝ)-a u-b u))/D
    let q:=longAssignedIntervalProbability F hF K m θ
    let s:=longAssignedSpokeProbability F hF K m θ
    0≤p₁ ∧ 0≤k₁ ∧ 0≤p₂ ∧ 0≤k₂ ∧ 0≤udens ∧
    2*p₁+2*k₁+2*p₂+2*k₂+udens≤1 ∧
    (∀u j,0≤q u j) ∧ (∀u,∑j,q u j≤1/8) ∧
    (∀u j,0≤s u j) ∧
    (∀u,∑j,s u j≤ intervalUncoveredProbability d (∑j,q u j)) :=by
  intro b a p₁ k₁ p₂ k₂ udens q s
  have h:=long_assigned_factor_concrete_sampling hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  dsimp only at h
  rcases h with ⟨hcol,hq,hQ,hs,hS,hpstar,hpstarU,ht,hts,htone,hks,hkp,hkk,hkeq,hp1,hk1,hp2,hk2,hu,hsum,hle⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hq hQ hs hS hp2 hk2 hu hle
  have hps:0≤p₂:=by
    dsimp only [p₂,b,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction]
    linarith [hp2]
  have hks':0≤k₂:=by
    dsimp only [k₂,a,longAssignedApproxMarkedWeight,ordinaryAssignedFraction]
    have hρpos:0≤ρ₀/(6*((m:ℝ)+1)):=by positivity
    linarith only [hk2,hρpos]
  refine ⟨hp1,hk1,hps,hks',?_,?_,?_,?_,?_,?_⟩
  · simpa only [udens,a,b,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hu
  · simpa only [p₁,k₁,p₂,k₂,udens,a,b,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hle
  · simpa only [q,longAssignedIntervalProbability,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hq
  · simpa only [q,longAssignedIntervalProbability,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hQ
  · simpa only [s,longAssignedSpokeProbability,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hs
  · simpa only [s,q,longAssignedSpokeProbability,longAssignedIntervalProbability,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hS
end Oberwolfach
