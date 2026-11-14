module

public import Oberwolfach.OrdinaryDeepDomainNeighbourhoodEvent
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
/-! The full-domain row and hub singleton tests can be added to any prior on
the original expanded sample and the same physical direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 9000000
set_option synthInstance.maxSize 8192
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_global_profiles_with_prior (ω ε:ℝ) (hω:0<ω) (hε:0<ε) (d q₀:ℕ) (hd:2≤d):
    ∃N:ℕ,∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],N≤Fintype.card V→Fintype.card U≤Fintype.card V→
      ω*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀(P F:SimpleGraph V) (π:Equiv.Perm V),permutationConflictGraph π (3*d)≤F→
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
      (j:Color) (pH:ℝ),(∀w,s w j=pH)→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ν:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-a≤((μ.sigma ρ).prod ν).probability E→
    1-a-1/(Fintype.card V:ℝ)^q₀≤((μ.sigma ρ).prod ν).probability (fun z=>E z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      RawOrdinaryRows P π d 3 Finset.univ (2*p) s j (ε*Fintype.card V) raw ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) raw):=by
  obtain ⟨N,hN⟩:=ordinary_three_domain_neighbourhood_common_event 1 ω ε (by norm_num) hω hε d q₀ hd
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU hωU P F π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj R _ ρ ν E a μ hE
  have hp1:2*p≤1:=by linarith
  let J:RawWheelOutcome V U Γ Color→Prop:=fun raw=>
    RawOrdinaryRows P π d 3 Finset.univ (2*p) s j (ε*Fintype.card V) raw ∧
      RawOrdinaryDomainIndices F π d 3 Finset.univ pH j (ε*Fintype.card U) raw
  let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>hp1) d hd q hq hQ s hs hS)
  have hraw:1-1/(Fintype.card V:ℝ)^q₀≤μraw.probability J:=by
    have hh:=hN V U Γ Color P F π Finset.univ Finset.univ (by simpa using hn)
      (by simp) (by simpa using (show (Fintype.card U:ℝ)≤Fintype.card V from Nat.cast_le.mpr hU))
      (by simpa using hωU) hconf hnoshort (2*p) (by linarith) hp1 q hq hQ s hs hS j pH hj
    convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  exact ordinary_expanded_add_raw_event_with_product_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ρ ν E J a (1/(Fintype.card V:ℝ)^q₀) hE hraw
end Oberwolfach
