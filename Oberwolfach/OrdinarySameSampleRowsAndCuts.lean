module

public import Oberwolfach.OrdinaryExpandedFixedTwoStepVortexTestsProductPrior
public import Oberwolfach.OrdinaryExpandedFixedVortexRimCuts

@[expose] public section
/-! Fixed and two-step balance tests and all-level rim cuts can be adjoined
to any prior on the same expanded sample and reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_same_sample_rows_and_cuts
    (h d:ℕ) (hd:2≤d) (α αcut pstar β ε ρ₀ εR εH χone χtwo χcut:ℝ)
    (hα:0<α) (hαcut:0<αcut) (hαcut1:αcut≤1/2) (hαcutα:αcut≤α/2)
    (hpstar:0<pstar) (hβ:0≤β) (hβα:β≤α/8) (hβ1:β≤1/4)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hεR:0<εR) (hεH:0<εH)
    (hχone:0<χone) (hχtwo:0<χtwo) (hχcut:0<χcut):
    ∃m₀:ℕ,1≤m₀ ∧ ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P F:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (1/2+α)*Fintype.card V≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:Vortex U P D β ε m) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→permutationConflictGraph π (3*d)≤F→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),pstar≤2*p→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (pH:ℝ) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (loss:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let κ:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-loss≤((μ.sigma ν).prod κ).probability E→
    1-(loss+χone+χtwo+χcut)≤((μ.sigma ν).prod κ).probability (fun z=>
      ((E z ∧ OrdinaryFixedVortexRowIndexEvent h d εR εH P F D m β ε Q π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
       OrdinaryVortexTwoStepRowIndexEvent h d εR εH P F D m β ε Q π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pstar) :=by
  obtain ⟨mRows,hmRows,hRows⟩:=ordinary_expanded_attach_fixed_and_two_step_vortex_tests_product_prior h d hd εR εH β ε ρ₀ χone χtwo
    hεR hεH hβ hβ1 hε hε1 hρ₀ hχone hχtwo
  obtain ⟨mCuts,hmCuts,hCuts⟩:=ordinary_expanded_fixed_vortex_rim_cuts α αcut pstar β ε ρ₀ χcut
    hα hαcut hαcut1 hαcutα hpstar hβ hβα hβ1 hε hε1 hρ₀ hχcut
  refine ⟨max mRows mCuts,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P F D m hreg hn hdegree hρlo hρhi hm Q π hπ hnoshort hF
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR q hq hQ s hs hS j pH hj R _ ν E loss μ κ hE
  have hD:(Fintype.card V:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤1/2+α by linarith) (show (0:ℝ)≤Fintype.card V by positivity)
    nlinarith only [hh,hdegree]
  let Prior:=fun z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)=>
    (E z ∧ OrdinaryFixedVortexRowIndexEvent h d εR εH P F D m β ε Q π hπ (2*p) pH s j
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
    OrdinaryVortexTwoStepRowIndexEvent h d εR εH P F D m β ε Q π hπ (2*p) pH s j
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))
  have hprior:1-(loss+χone+χtwo)≤((μ.sigma ν).prod κ).probability Prior:=by
    exact hRows V U Γ Color P F D m hreg hn hD hρlo hρhi (by omega) Q π hπ hnoshort hF
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS j pH hj ν κ E loss hE
  exact hCuts V U Γ Color P D m hreg hn hdegree hρlo hρhi (by omega) Q
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpstarR d hd q hq hQ s hs hS ν Prior (loss+χone+χtwo) hprior
end Oberwolfach
