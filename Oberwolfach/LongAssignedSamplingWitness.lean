module

public import Oberwolfach.LongAssignedSamplingRecipe
public import Oberwolfach.LongAssignedConcreteSampling

@[expose] public section
/-! The actual long-class interval and spoke recipe supplies the five
physical probabilities used by the shared categorical exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_class_sampling_witness {n:ℕ} (hn:0<n)
    {U:Type} [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (K:ℕ) (hK:0<K) (m d:ℕ) (hm:7≤m) (hd:2≤d) (θ ρ₀ ρ D:ℝ)
    (hθ0:0≤θ) (hθ:θ≤1/100) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*Fintype.card U) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
    (hclass:∀u,factorPreparationClass (F u) K=none):
    ∃ (p k p₂ k₂ udens:ℝ),0≤p ∧ 0≤k ∧ 0≤p₂ ∧ 0≤k₂ ∧ 0≤udens ∧
      2*p+2*k+2*p₂+2*k₂+udens=ρ ∧ 2*p=ρ*(1/100:ℝ) ∧
      2*k=ρ*((1/100:ℝ)/(m:ℝ)) ∧ ρ₀/8≤p₂ ∧ ρ₀/(6*((m:ℝ)+1))≤k₂ ∧
      p₂*D=∑w,longAssignedApproxOrdinaryWeight F hF K m θ w ∧
      k₂*D=∑w,longAssignedApproxMarkedWeight F hF K m θ w ∧
      udens*D=2*∑w,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-longAssignedApproxMarkedWeight F hF K m θ w-longAssignedApproxOrdinaryWeight F hF K m θ w) ∧
      0<ρ₀*((1/100:ℝ)/(m:ℝ))/2 ∧ ρ₀*((1/100:ℝ)/(m:ℝ))/2≤k ∧
    let q:=longAssignedIntervalProbability F hF K m θ
    let sco:=longAssignedSpokeProbability F hF K m θ;
      (∀w j,0≤q w j) ∧ (∀w,∑j,q w j≤1/8) ∧
      (∀w j,0≤sco w j) ∧ (∀w,∑j,sco w j≤ intervalUncoveredProbability d (∑j,q w j)) ∧
      (∀w,q w false=(1/100:ℝ)/(m:ℝ) ∧ sco w false=1/100) :=by
  let av:=longAssignedApproxMarkedWeight F hF K m θ
  let bv:=longAssignedApproxOrdinaryWeight F hF K m θ
  let p:=ρ*(1/100:ℝ)/2
  let k:=ρ*((1/100:ℝ)/(m:ℝ))/2
  let p₂:=(∑w:U,bv w)/D
  let k₂:=(∑w:U,av w)/D
  let udens:=2*(∑w:U,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-av w-bv w))/D
  have hh:=long_assigned_factor_concrete_sampling hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρhi hD hsize hcut hclass
  rcases hh with ⟨hcol,hq,hQ,hs,hS,hRef,hRefU,ht,hts,ht1,hkstar,hkp,hkk,heq,hp,hk,hp₂,hk₂,hu,hbal,hle⟩
  have hh':0≤p ∧ 0≤k ∧ ρ₀/8≤p₂ ∧ ρ₀/(6*((m:ℝ)+1))≤k₂ ∧ 0≤udens ∧
      2*p+2*k+2*p₂+2*k₂+udens=ρ ∧ 0<ρ₀*((1/100:ℝ)/(m:ℝ))/2 ∧
      ρ₀*((1/100:ℝ)/(m:ℝ))/2≤k :=by
    dsimp only [p,k,p₂,k₂,udens,av,bv,longAssignedApproxMarkedWeight,longAssignedApproxOrdinaryWeight,ordinaryAssignedFraction]
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
      (show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨hp,hk,hp₂,hk₂,hu,hbal,hkstar,hkk⟩)
  have hrecipe:(∀w j,0≤longAssignedIntervalProbability F hF K m θ w j) ∧
      (∀w,∑j,longAssignedIntervalProbability F hF K m θ w j≤1/8) ∧
      (∀w j,0≤longAssignedSpokeProbability F hF K m θ w j) ∧
      (∀w,∑j,longAssignedSpokeProbability F hF K m θ w j≤
        intervalUncoveredProbability d (∑j,longAssignedIntervalProbability F hF K m θ w j)) :=by
    simpa only [longAssignedIntervalProbability,longAssignedSpokeProbability,longAssignedApproxMarkedWeight,
      longAssignedApproxOrdinaryWeight,ordinaryAssignedFraction,Finset.mem_filter,Finset.mem_univ,true_and] using
      (show _ ∧ _ ∧ _ ∧ _ from ⟨hq,hQ,hs,hS⟩)
  have hp₂eq:p₂*D=∑w,bv w:=by dsimp [p₂];field_simp
  have hk₂eq:k₂*D=∑w,av w:=by dsimp [k₂];field_simp
  have hueq:udens*D=2*∑w,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-av w-bv w):=by dsimp [udens];field_simp
  have hp₂:0≤p₂:=le_trans (by positivity) hh'.2.2.1
  have hk₂:0≤k₂:=le_trans (by positivity) hh'.2.2.2.1
  refine ⟨p,k,p₂,k₂,udens,hh'.1,hh'.2.1,hp₂,hk₂,hh'.2.2.2.2.1,hh'.2.2.2.2.2.1,?_,?_,
    hh'.2.2.1,hh'.2.2.2.1,hp₂eq,hk₂eq,hueq,hh'.2.2.2.2.2.2.1,hh'.2.2.2.2.2.2.2,
    hrecipe.1,hrecipe.2.1,hrecipe.2.2.1,hrecipe.2.2.2,?_⟩
  · dsimp [p];ring
  · dsimp [k];ring
  · intro w
    simp [longAssignedIntervalProbability,longAssignedSpokeProbability]
end Oberwolfach
