module

public import Oberwolfach.OrdinaryExpandedDomainProfiles

@[expose] public section
/-! High-probability fixed-domain profiles are added to any earlier event
on the same expanded sample and dependent second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_domain_profiles_high_probability
    (K ω ε:ℝ) (hK:1≤K) (hω:0<ω) (hε:0<ε) (d q₀:ℕ) (hd:2≤d):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P F:SimpleGraph V) (π:Equiv.Perm V) (I:Finset V) (J:Finset U),N≤I.card →
      (Fintype.card V:ℝ)≤K*I.card → (Fintype.card U:ℝ)≤K*I.card → ω*I.card≤(J.card:ℝ) →
      permutationConflictGraph π (3*d)≤F → (∀x l,0<l→l<2*d+1→(π^l) x≠x) →
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
      (j:Color) (pH:ℝ),(∀w,s w j=pH) →
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E →
    1-(εE+1/(I.card:ℝ)^q₀)≤(μ.sigma ν).probability (fun z=>E z ∧
      RawOrdinaryRows P π d 2 I (2*p) s j (ε*I.card) (fun e=>expandedOrdinarySelectedCollapse e (z.1 e)) ∧
      RawOrdinaryDomainIndices F π d 3 J pH j (ε*J.card) (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))):=by
  obtain ⟨N,hN⟩:=ordinary_two_domain_neighbourhood_common_event K ω ε hK hω hε d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F π I J hn hV hU hJ hF hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj R _ ν E εE μ hE
  have hp0:0≤2*p:=by positivity
  have hp1:2*p≤1:=by linarith
  have hProfile:=hN V U Γ Color P F π I J hn hV hU hJ hF hnoshort
    (2*p) hp0 hp1 q hq hQ s hs hS j pH hj
  have hProfile':1-1/(I.card:ℝ)^q₀≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p)
      (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)).probability
      (fun σ=>RawOrdinaryRows P π d 2 I (2*p) s j (ε*I.card) σ ∧
        RawOrdinaryDomainIndices F π d 3 J pH j (ε*J.card) σ):=by
    convert hProfile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact ordinary_expanded_add_domain_profiles P F π I J d hd pH (ε*I.card) (ε*J.card) j
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS ν E εE (1/(I.card:ℝ)^q₀) hProfile' hE
end Oberwolfach
