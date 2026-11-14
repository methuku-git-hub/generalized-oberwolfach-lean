module

public import Oberwolfach.OrdinaryNamedDeepCoverSeparateLoadProbability
public import Oberwolfach.OrdinaryReferenceCentreFromRegularHost

@[expose] public section
/-! The ordinary deep-cover event specialized to the regular host and the
    reserved-class marginals, with its constants chosen before the order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_cover_separate_load_regular_host_probability
    (r:ℕ) (hr:4≤r) (α pmin smin ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω):
    ∃K:ℕ,0<K ∧ ∃a ε₀ ρdeep θdeep:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρdeep ∧ 0<θdeep ∧
    ∀aLoad:ℝ,0<aLoad→aLoad≤a→∀Dmax d q₀:ℕ,∀hd:2≤d,∃N:ℕ,
    ∀n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U],
    ∀(P Fbad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (J:Finset U),
    (J.card:ℝ)≤a*n → (ω*n≤((Finset.univ\J).card:ℝ)) → Fintype.card U≤n →
    (∀v,(cycleThreshold r+α)*n≤(P.degree v:ℝ)) → (∀v,Fbad.degree v≤Dmax) →
    permutationConflictGraph π (3*d)≤Fbad →
    (∀x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀(ρ s pR:ℝ) (D:ℕ) (hρ0:0<ρ) (hρ1:ρ≤1) (hs0:smin≤s) (hs1:s≤1) (hpR:pmin≤pR) (hpR1:pR≤1),
    (n:ℝ)/2≤D → P.IsRegularOfDegree D → ρ*D=2*(Fintype.card U:ℝ) → pR=ρ*s →
    ∀(q:U→Bool→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (sp:U→Bool→ℝ) (hs:∀w j,0≤sp w j)
      (hS:∀w,∑j,sp w j≤ intervalUncoveredProbability d (∑g,q w g)),
    (∀w,sp w false=s) →
    1-1/(n:ℝ)^q₀≤(FiniteLaw.pi (rawWheelLaw (V:=Fin n) (fun _=>pR)
      (fun _=>le_trans (le_of_lt hpmin) hpR) (fun _=>hpR1) d hd q hq hQ sp hs hS)).probability
      (OrdinaryDeepCoverSeparateLoadEvent (r-1) K a aLoad ρdeep θdeep P Fbad J π d false):=by
  let pstar:=min pmin smin
  have hpstar:0<pstar:=lt_min hpmin hsmin
  have hpstar1:pstar≤1:=(min_le_right _ _).trans hsmin1
  obtain ⟨K,hK,a,ε₀,ρdeep,θdeep,ha,hε,hρ,hθ,hMain⟩:=
    ordinary_named_deep_cover_separate_load_high_probability (r-1) (by omega) α pstar ω hα hpstar hpstar1 hω
  refine ⟨K,hK,a,ε₀,ρdeep,θdeep,ha,hε,hρ,hθ,?_⟩
  intro aLoad hloadPos hloadLe Dmax d q₀ hd
  obtain ⟨N,hN⟩:=hMain aLoad hloadPos hloadLe Dmax d q₀ hd
  refine ⟨N,?_⟩
  intro n hn U _ _ P Fbad π J hJ hUlo hU hP hF hconf hnoshort ρ s pR D hρ0 hρ1 hs0 hs1 hpR hpR1 hD hreg hsize hpEq q hq hQ sp hs hS hsp
  have hpstarR:pstar≤pR:=(min_le_left _ _).trans hpR
  have hpstarH:pstar≤s:=(min_le_right _ _).trans hs0
  have hnear:∀v,|(P.degree v:ℝ)-(D:ℝ)|≤0*n:=by intro v;rw [hreg v];simp
  have hcentre:pR*(D:ℝ)=2*(Fintype.card U:ℝ)*s:=by rw [hpEq]; calc
    (ρ*s)*(D:ℝ)=s*(ρ*D):=by ring
    _=2*(Fintype.card U:ℝ)*s:=by rw [hsize];ring
  have hP':∀v,(cycleThreshold ((r-1)+1)+α)*Fintype.card (Fin n)≤(P.degree v:ℝ):=by
    simpa only [Nat.sub_add_cancel (by omega : 1≤r),Fintype.card_fin] using hP
  have hh:=hN (Fin n) U Bool Bool P Fbad π J (by simpa using hn) (by simpa using hJ)
    (by simpa using hUlo) (by simpa using hU) hP' hF hconf hnoshort
    pR s D 0 hpstarR hpR1 hpstarH hs1 (by simpa using hD) (by norm_num) (le_of_lt hε)
    (by simpa using hnear) hcentre q hq hQ sp hs hS false hsp
  simpa only [Fintype.card_fin] using hh
end Oberwolfach
