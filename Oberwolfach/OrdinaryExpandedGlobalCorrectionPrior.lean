module

public import Oberwolfach.OrdinaryGlobalCorrectionEventsProbability
public import Oberwolfach.OrdinaryExpandedRawCoinEventProductPrior

@[expose] public section
/-! Attach global correction tests and cuts to any prior on the expanded
sample and the same orientation coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_global_correction_with_prior
    (α pstar ω:ℝ) (hα:0<α) (hα1:α≤1/2) (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω):
    ∃δ h:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧
    ∀(ε L:ℝ),0<ε→0≤L→∀d q₀:ℕ,∀hd:2≤d,∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀(P F:SimpleGraph V), (∀v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ))→(∀v,(F.degree v:ℝ)≤L)→
    ∀(π:Equiv.Perm V),permutationConflictGraph π (3*d)≤F→
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),pstar≤2*p→pstar≤pH→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color),(∀w,s w j=pH)→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-a≤((μ.sigma ρ).prod ν).probability E→
    1-a-2/(Fintype.card V:ℝ)^q₀≤((μ.sigma ρ).prod ν).probability (fun z=>E z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      RawOrdinaryRows P π d 2 Finset.univ (2*p) s j (ε*Fintype.card V) raw ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) raw ∧
      OrdinaryTriangleReferenceMatrixCuts P F π d j δ h raw z.2):=by
  obtain ⟨δ,h,hδ,hδsmall,hh,hmain⟩:=ordinary_global_correction_events_probability α pstar ω hα hα1 hpstar hpstar1 hω
  refine ⟨δ,h,hδ,hδsmall,hh,?_⟩
  intro ε L hε hL d q₀ hd
  obtain ⟨N,hmain⟩:=hmain ε L hε hL d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUlo hUhi P F hP hF π hconf hnoshort p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH
    q hq hQ s hs hS j hj R _ ρ E a μ ν hE
  have hp2:0≤2*p:=by positivity
  have hp21:2*p≤1:=by linarith
  let J:RawWheelOutcome V U Γ Color×(Sym2 V→Bool)→Prop:=fun z=>
    RawOrdinaryRows P π d 2 Finset.univ (2*p) s j (ε*Fintype.card V) z.1 ∧
    RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) z.1 ∧
    OrdinaryTriangleReferenceMatrixCuts P F π d j δ h z.1 z.2
  have hJ:=hmain V U Γ Color hn hUlo hUhi P F hP hF π hconf hnoshort (2*p) pH hp2 hp21 hpR hpH
    q hq hQ s hs hS j hj
  have hout:=ordinary_expanded_add_raw_coin_event_with_product_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E J a (2/(Fintype.card V:ℝ)^q₀) hE hJ
  convert hout using 1 <;> congr! 12 <;> exact Subsingleton.elim _ _
end Oberwolfach
