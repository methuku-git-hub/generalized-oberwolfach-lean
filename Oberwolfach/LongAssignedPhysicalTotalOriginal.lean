module

public import Oberwolfach.LongActualRawLawParameters

@[expose] public section
/-! The physical marginal of the assigned long-cycle sample has exactly
its original density, not merely a density bounded by one. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_assigned_physical_total_original {U:Type} [Fintype U] {n:ℕ} (hn:0<n)
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
    let udens:=2*(∑u,(1-1/100-(1/100)/(m:ℝ)-a u-b u))/D;
    2*p₁+2*k₁+2*p₂+2*k₂+udens=ρ :=by
  intro b a p₁ k₁ p₂ k₂ udens
  have h:=long_assigned_factor_concrete_sampling hn F hF Allowed hAllowed K hK m d hm hd θ ρ₀ ρ D
    hθ0 hθ hρ₀ hρlo hρ1 hD hsize hcut hclass
  dsimp only at h
  rcases h with ⟨hcol,hq,hQ,hs,hS,hpstar,hpstarU,ht,hts,htone,hks,hkp,hkk,hkeq,hp1,hk1,hp2,hk2,hu,hsum,hle⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hsum
  simpa only [p₁,k₁,p₂,k₂,udens,a,b,longAssignedApproxOrdinaryWeight,longAssignedApproxMarkedWeight,ordinaryAssignedFraction] using hsum
end Oberwolfach
