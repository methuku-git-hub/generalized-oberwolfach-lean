module

public import Oberwolfach.OrdinaryDeepDomainNeighbourhoodEvent
public import Oberwolfach.OrdinaryTriangleReferenceJoint

@[expose] public section
/-! Global row tests and the rim and spoke correction cuts occur together
on the same original sample and the same orientation coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_global_correction_events_probability
    (α pstar ω:ℝ) (hα:0<α) (hα1:α≤1/2) (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω):
    ∃δ h:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧
    ∀(ε L:ℝ),0<ε→0≤L→∀d q₀:ℕ,∀hd:2≤d,∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀(P F:SimpleGraph V), (∀v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ))→(∀v,(F.degree v:ℝ)≤L)→
    ∀(π:Equiv.Perm V),permutationConflictGraph π (3*d)≤F→
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(pR pH:ℝ) (hpR:0≤pR) (hpR1:pR≤1),pstar≤pR→pstar≤pH→
    ∀(q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g))
      (j:Color),(∀u,s u j=pH)→
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 V=>pR) (fun _=>hpR) (fun _=>hpR1) d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-2/(Fintype.card V:ℝ)^q₀≤(μ.prod ν).probability (fun z=>
      RawOrdinaryRows P π d 2 Finset.univ pR s j (ε*Fintype.card V) z.1 ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) z.1 ∧
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2):=by
  obtain ⟨δ,h,hδ,hδsmall,hh,hcuts⟩:=ordinary_reference_large_cuts α pstar ω hα hα1 hpstar hpstar1 hω
  refine ⟨δ,h,hδ,hδsmall,hh,?_⟩
  intro ε L hε hL d q₀ hd
  obtain ⟨Nr,hr⟩:=ordinary_three_domain_neighbourhood_common_event 1 ω ε (by norm_num) hω hε d q₀ hd
  obtain ⟨Nc,hc⟩:=hcuts L hL d q₀ hd
  refine ⟨max Nr Nc,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUlo hUhi P F hP hF π hconf hnoshort pR pH hpR hpR1 hpRlo hpHlo
    q hq hQ s hs hS j hj μ ν
  have hr':1-1/(Fintype.card V:ℝ)^q₀≤μ.probability (fun σ=>
      RawOrdinaryRows P π d 3 Finset.univ pR s j (ε*Fintype.card V) σ ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) σ):=by
    have hh:=hr V U Γ Color P F π Finset.univ Finset.univ (by simpa using (show Nr≤Fintype.card V by omega))
      (by simp) (by simpa using (show (Fintype.card U:ℝ)≤Fintype.card V by exact_mod_cast hUhi))
      (by simpa using hUlo) hconf hnoshort pR hpR hpR1 q hq hQ s hs hS j pH hj
    simpa only [Finset.card_univ] using hh
  have hc':1-1/(Fintype.card V:ℝ)^q₀≤(μ.prod ν).probability (fun z=>
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2):=by
    exact hc V U Γ Color (by omega) hUlo hUhi P F hP hF π hnoshort pR pH hpR hpR1 hpRlo hpHlo q hq hQ s hs hS j hj
  have hr'':1-1/(Fintype.card V:ℝ)^q₀≤(μ.prod ν).probability (fun z=>
      RawOrdinaryRows P π d 3 Finset.univ pR s j (ε*Fintype.card V) z.1 ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) z.1):=by
    change 1-1/(Fintype.card V:ℝ)^q₀≤(μ.prod ν).probability (fun z=>
      (fun σ=>RawOrdinaryRows P π d 3 Finset.univ pR s j (ε*Fintype.card V) σ ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) σ) z.1)
    have hproj:=finiteLaw_prod_first_probability μ ν (fun σ=>RawOrdinaryRows P π d 3 Finset.univ pR s j (ε*Fintype.card V) σ ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) σ)
    rw [←hproj] at hr'
    convert hr' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hjoint:1-1/(Fintype.card V:ℝ)^q₀-1/(Fintype.card V:ℝ)^q₀≤(μ.prod ν).probability (fun z=>
      (RawOrdinaryRows P π d 3 Finset.univ pR s j (ε*Fintype.card V) z.1 ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) z.1) ∧
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2):=
    (sub_le_sub_right hr'' _).trans (finiteLaw_good_intersection (μ.prod ν) _ _ _ hc')
  have hnum:1-2/(Fintype.card V:ℝ)^q₀=1-1/(Fintype.card V:ℝ)^q₀-1/(Fintype.card V:ℝ)^q₀:=by ring
  rw [hnum]
  apply hjoint.trans
  apply finiteLaw_probability_mono
  intro z hz
  refine ⟨?_,hz.1.2,hz.2⟩
  intro S J hS hJ
  exact hz.1.1 S J (by omega) (by omega)
end Oberwolfach
