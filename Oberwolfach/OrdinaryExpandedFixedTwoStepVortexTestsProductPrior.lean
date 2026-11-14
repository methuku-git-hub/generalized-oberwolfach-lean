module

public import Oberwolfach.OrdinaryExpandedTwoStepVortexTestsProductPrior
public import Oberwolfach.OrdinaryExpandedVortexTestsProductPrior
public import Oberwolfach.OrdinaryFixedVortexRowIndexEvent
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
/-! Join all ordinary vortex row and hub tests to any existing event on the
same expanded sample, including a dependent second stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_attach_fixed_and_two_step_vortex_tests_product_prior
    (h d:ℕ) (hd:2≤d) (εR εH β ε ρ₀ χone χtwo:ℝ)
    (hεR:0<εR) (hεH:0<εH) (hβ:0≤β) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hχone:0<χone) (hχtwo:0<χtwo):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P F:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→permutationConflictGraph π (3*d)≤F→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (pH:ℝ) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤((μ.sigma ν).prod κ).probability E→
    1-(εE+χone+χtwo)≤((μ.sigma ν).prod κ).probability (fun z=>(E z ∧
      OrdinaryFixedVortexRowIndexEvent h d εR εH P F D m β ε Q π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryVortexTwoStepRowIndexEvent h d εR εH P F D m β ε Q π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))):=by
  obtain ⟨mOne,hmOne,hOne⟩:=ordinary_expanded_attach_fixed_vortex_tests_product_prior h d hd εR εH β ε ρ₀ χone
    hεR hεH hβ hβ1 hε hε1 hρ₀ hχone
  obtain ⟨mTwo,hmTwo,hTwo⟩:=ordinary_expanded_attach_two_step_vortex_tests_product_prior h d hd εR εH β ε ρ₀ χtwo
    hεR hεH hβ hβ1 hε hε1 hρ₀ hχtwo
  refine ⟨max mOne mTwo,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F D m hreg hn hD hρlo hρhi hm Q π hπ hnoshort hF
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj R _ ν κ E εE μ hE
  let First:=fun z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)=>
    E z ∧ OrdinaryFixedVortexRowIndexEvent h d εR εH P F D m β ε Q π hπ (2*p) pH s j
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))
  have hfirst:1-(εE+χone)≤((μ.sigma ν).prod κ).probability First:=by
    exact hOne V U Γ Color P F D m hreg hn hD hρlo hρhi (by omega) Q π hπ hnoshort hF
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj ν κ E εE hE
  have hh:=hTwo V U Γ Color P F D m hreg hn hD hρlo hρhi (by omega) Q π hπ hnoshort hF
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj ν κ First (εE+χone) hfirst
  exact hh
end Oberwolfach
