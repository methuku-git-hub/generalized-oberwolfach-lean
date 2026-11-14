module

public import Oberwolfach.OrdinaryTriangleOuterDegreeRegularHostProbability
public import Oberwolfach.OrdinaryAssignedProtectedReservoirHighProbability
public import Oberwolfach.OrdinaryAssignedParentSamplingBalance

@[expose] public section
/-! On an original assigned sample, the adaptive finite triangle cover and
    the protected reservoir are simultaneously available. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 32768
set_option maxRecDepth 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedCoverReservoirFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_cover_and_reservoir_high_probability
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
      (K:ℕ) (i₀:Fin K) (rsv θ c ρ p k p₂ k₂ u:ℝ) (D:ℕ),
    (hp:0≤p) → (hk:0≤k) → (hp₂:0≤p₂) → (hk₂:0≤k₂) → (hu:0≤u) →
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) →
    0<ρ → ρ≤1 → smin≤rsv → rsv≤1 → pmin≤2*p →
    (n:ℝ)/2≤D → (D:ℝ)≤2*n → P.IsRegularOfDegree D →
    ρ*D=2*(Fintype.card U:ℝ) → 2*p=ρ*rsv →
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
    ∀(hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)),
    let μ:=FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS);
    1-1/(n:ℝ)^q₀-(1/(n:ℝ)+2/(n:ℝ)^2)≤μ.probability (fun σ=>
      OrdinaryTriangleFiniteCoverOuterDegreeEvent κ P Fbad J π d false σ ∧
      OrdinaryUniformProtectedReservoirEvent 3 mRes tRes fRes aRes bRes εabs
        (rawWheelGraph P σ\Fbad) Fbad (rawWheelSpokes π d σ false)) := by
  obtain ⟨κ,hκ,hcover⟩:=ordinary_triangle_cover_outer_degree_regular_host_high_probability α pmin smin ω hα hpmin hsmin hsmin1 hω
  obtain ⟨εabs,εtrans,εsample,hεabs,hεtrans,hεsample,hres⟩:=
    ordinary_assigned_protected_reservoir_high_probability 3 d (by omega) hd α pmin smin (Dmax:ℝ) ω
      hα hpmin hsmin hsmin1 hω (by positivity)
  refine ⟨κ,εabs,εtrans,εsample,hκ,hεabs,hεtrans,hεsample,?_⟩
  intro mRes
  obtain ⟨aRes,bRes,tRes₀,htRes₀,hres⟩:=hres mRes
  refine ⟨aRes,bRes,tRes₀,htRes₀,?_⟩
  intro tRes fRes q₀
  obtain ⟨Ncover,hcover⟩:=hcover Dmax d q₀ hd
  obtain ⟨Nres,hres⟩:=hres tRes fRes
  refine ⟨max Ncover Nres,?_⟩
  intro n hn hn0 U _ _ P Fbad π J hJ hlo hU hP hFdeg hconf hshort F hF K i₀ rsv θ c ρ p k p₂ k₂ u D
    hp hk hp₂ hk₂ hu hsum hρ hρ1 hrsv hrsv1 hpR hDlo hDhi hreg hsize hpEq q s hq hQ hs hS μ
  have hUlo : ω*n≤(Fintype.card U:ℝ) := hlo.trans (by exact_mod_cast Finset.card_le_univ (Finset.univ\J))
  have hFb : ∀v,(Fbad.degree v:ℝ)≤Dmax := fun v=>by exact_mod_cast hFdeg v
  have hnear : ∀v,|(P.degree v:ℝ)-(D:ℝ)|≤εsample*n := by
    intro v
    rw [hreg v]
    simp only [sub_self,abs_zero]
    positivity
  have hrecipe:=ordinary_assigned_parent_sampling_balance F hF i₀ rsv θ c ρ D p k p₂ k₂ u
    hp hk hp₂ hk₂ hu hsum hsize hpEq
  have hspoke:∀w,s w false=rsv:=hrecipe.2.2.2
  have hC:=hcover n (le_trans (le_max_left _ _) hn) U P Fbad π J hJ hlo hU hP hFdeg hconf hshort
    ρ rsv (2*p) D hρ hρ1 hrsv hrsv1 hpR hrecipe.2.1 hDlo hreg hsize hpEq q hq hQ s hs hS hspoke
  have hR:=hres n (le_trans (le_max_right _ _) hn) U hU hUlo P Fbad π hconf hshort hFb hP
    D hDlo hDhi hnear (2*p) hpR hrecipe.2.1 F hF K i₀ rsv θ c hrsv hrsv1 hq hQ hs hS
  let C:RawWheelOutcome (Fin n) U Bool Bool→Prop:=OrdinaryTriangleFiniteCoverOuterDegreeEvent κ P Fbad J π d false
  let R:RawWheelOutcome (Fin n) U Bool Bool→Prop:=fun σ=>
    OrdinaryUniformProtectedReservoirEvent 3 mRes tRes fRes aRes bRes εabs
      (rawWheelGraph P σ\Fbad) Fbad (rawWheelSpokes π d σ false)
  have hC':1-1/(n:ℝ)^q₀≤μ.probability C:=by
    convert hC using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  have hR':1-(1/(n:ℝ)+2/(n:ℝ)^2)≤μ.probability R:=by
    convert hR using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
  exact (sub_le_sub_right hC' _).trans (finiteLaw_good_intersection μ C R _ hR')
end Oberwolfach
