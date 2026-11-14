module

public import Oberwolfach.OrdinaryAssignedCoverReservoirProbability
public import Oberwolfach.OrdinaryAssignedSamplingNamedWitness

@[expose] public section
/-! The original factor-class assumptions supply the categorical sampling
    recipe and the simultaneous adaptive cover and protected reservoir. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 32768
set_option maxRecDepth 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedCoverRecipeFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_cover_reservoir_from_factor_recipe
    (α pmin smin ω : ℝ) (hα : 0<α) (hpmin : 0<pmin) (hsmin : 0<smin)
    (hsmin1 : smin≤1) (hω : 0<ω) (d Dmax : ℕ) (hd : 2≤d) :
    ∃ κ εabs εtrans εsample : ℝ, 0<κ ∧ 0<εabs ∧ 0<εtrans ∧ 0<εsample ∧
    ∀mRes:ℕ,∃aRes bRes tRes₀:ℕ,1≤tRes₀ ∧ ∀tRes fRes q₀:ℕ,∃N:ℕ,
    ∀n:ℕ,N≤n→0<n→∀(U:Type) [Fintype U] [LinearOrder U],
    ∀(P Fbad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (J:Finset U),
    (J.card:ℝ)≤κ*n → ω*n≤((Finset.univ\J).card:ℝ) → Fintype.card U≤n →
    (∀v,(cycleThreshold 3+α)*n≤(P.degree v:ℝ)) → (∀v,Fbad.degree v≤Dmax) →
    permutationConflictGraph π (3*d)≤Fbad →
    (∀x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ:ℝ) (D:ℕ),
    0≤rsv → rsv≤1/100 → 0<θ → θ≤1/100 → 8≤c → 1/θ≤d →
    0<ρ → ρ≤1 → smin≤rsv → pmin≤ρ*rsv →
    rsv≤1/(2*(K:ℝ)) → (∀u,factorPreparationClass (F u) K=some i₀) →
    (n:ℝ)/2≤D → (D:ℝ)≤2*n → P.IsRegularOfDegree D → ρ*D=2*(Fintype.card U:ℝ) →
    ∃ u:ℝ,0≤u ∧
      0≤ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D ∧
      ρ*rsv+2*ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D+u=ρ ∧
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
    ∃(hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    ∃(hpR:0≤2*(ρ*rsv/2)) (hpR1:2*(ρ*rsv/2)≤1),
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>2*(ρ*rsv/2)) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS);
    1-1/(n:ℝ)^q₀-(1/(n:ℝ)+2/(n:ℝ)^2)≤μ.probability (fun σ=>
      OrdinaryTriangleFiniteCoverOuterDegreeEvent κ P Fbad J π d false σ ∧
      OrdinaryUniformProtectedReservoirEvent 3 mRes tRes fRes aRes bRes εabs
        (rawWheelGraph P σ\Fbad) Fbad (rawWheelSpokes π d σ false)) := by
  obtain ⟨κ,εabs,εtrans,εsample,hκ,hεabs,hεtrans,hεsample,hMain⟩:=
    ordinary_assigned_cover_and_reservoir_high_probability α pmin smin ω hα hpmin hsmin hsmin1 hω d Dmax hd
  refine ⟨κ,εabs,εtrans,εsample,hκ,hεabs,hεtrans,hεsample,?_⟩
  intro mRes
  obtain ⟨aRes,bRes,tRes₀,htRes₀,hMain⟩:=hMain mRes
  refine ⟨aRes,bRes,tRes₀,htRes₀,?_⟩
  intro tRes fRes q₀
  obtain ⟨N,hMain⟩:=hMain tRes fRes q₀
  refine ⟨N,?_⟩
  intro n hn hn0 U _ _ P Fbad π J hJ hlo hU hP hFdeg hconf hshort F hF Allowed hAllowed
    K hK i₀ rsv θ c ρ D hs0 hs1 hθ hθ1 hc hda hρ hρ1 hsminR hpminR hsclass hclass hDlo hDhi hreg hsize
  have hD : (0:ℝ)<D := by
    have hnR : (0:ℝ)<n := by exact_mod_cast hn0
    linarith
  obtain ⟨u,hu,hp₂,hp₂lo,hsum,hud,hq,hQ,hs,hS,hfalse⟩:=ordinary_assigned_named_sampling_witness
    hn0 F hF Allowed hAllowed K hK i₀ rsv θ c ρ D d hd hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize hsclass hclass
  have hp : 0≤ρ*rsv/2 := by positivity
  have hsum' : 2*(ρ*rsv/2)+2*0+2*ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D+2*0+u≤1 := by linarith
  have hR : 0≤2*(ρ*rsv/2) := by positivity
  have hR1 : 2*(ρ*rsv/2)≤1 := by linarith
  have hpminR' : pmin≤2*(ρ*rsv/2) := by nlinarith
  refine ⟨u,hu,hp₂,hsum,hq,hQ,hs,hS,hR,hR1,?_⟩
  intro μ
  have hh:=hMain n hn hn0 U P Fbad π J hJ hlo hU hP hFdeg hconf hshort F hF K i₀ rsv θ c ρ
    (ρ*rsv/2) 0 (ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D) 0 u D hp (by norm_num) hp₂ (by norm_num)
    hu hsum' hρ hρ1 hsminR (by linarith) hpminR' hDlo hDhi hreg hsize (by ring) hq hQ hs hS
  dsimp only at hh
  exact hh
end Oberwolfach
