module

public import Oberwolfach.OrdinaryExpandedVortexTriangleSeparateLoadFineProductPriorCapped
public import Oberwolfach.OrdinarySameSampleRowsAndCuts

@[expose] public section
/-! Retain an arbitrary product-law prior while adjoining triangle fine cover,
all-level row tests and oriented rim cuts on the same coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_fine_rows_cuts_product_prior
    (α ρ₀ pmin cap:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1) (hcap:0<cap):
    ∃κ:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ ∀aLoad:ℝ,0<aLoad→aLoad≤κ→∀(ε χdeep:ℝ),0<ε→ε<1/4→ε≤κ→ε≤ρ₀/16→0<χdeep→
    ∀(β:ℝ),0≤β→β≤1/4→β≤α/8→β≤κ→
    ∀(d:ℕ) (hd:2≤d) (εR εH χone χtwo χcut:ℝ),0<εR→0<εH→0<χone→0<χtwo→0<χcut→
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold 3≤θhost→(θhost+α)*Fintype.card V≤D→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (loss:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let κcoins:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)
    let αcut:=min (α/4) (1/4:ℝ);
    1-loss≤((μ.sigma ν).prod κcoins).probability E→
    1-(loss+χdeep+χone+χtwo+χcut)≤((μ.sigma ν).prod κcoins).probability (fun z=>
      (((E z ∧ OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin) :=by
  obtain ⟨κ,hκ,hκ1,hκcap,htri⟩:=ordinary_expanded_vortex_triangle_separate_load_fine_product_prior_capped
    α ρ₀ pmin cap hα hρ₀ hpmin hpmin1 hcap
  refine ⟨κ,hκ,hκ1,hκcap,?_⟩
  intro aLoad haLoad haκ ε χdeep hε hε1 hεκ hερ hχdeep β hβ hβ1 hβα hβκ d hd εR εH χone χtwo χcut hεR hεH hχone hχtwo hχcut
  obtain ⟨vTri,hvTri,htri⟩:=htri aLoad haLoad haκ ε χdeep hε hε1 hεκ hερ hχdeep β hβ hβ1 hβα hβκ d hd
  let αcut:=min (α/4) (1/4:ℝ)
  have hcut:0<αcut:=by dsimp [αcut]; positivity
  have hcut1:αcut≤1/2:=by dsimp [αcut]; exact le_trans (min_le_right _ _) (by norm_num)
  have hcutα:αcut≤α/2:=by dsimp [αcut]; have hh:=min_le_left (α/4) (1/4:ℝ); linarith
  obtain ⟨vRows,hvRows,hrows⟩:=ordinary_same_sample_rows_and_cuts 3 d hd α αcut pmin β ε ρ₀ εR εH χone χtwo χcut
    hα hcut hcut1 hcutα hpmin hβ hβα hβ1 hε hε1 hρ₀ hεR hεH hχone hχtwo hχcut
  refine ⟨max vTri vRows,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj R _ ν E loss μ κcoins αcut' hE
  let Prior:=fun z:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)=>
    E z ∧ OrdinaryFixedVortexTriangleSeparateLoadFineCoverEvent d κ aLoad P D vsize β ε Q π hπ j
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))
  have hprior:1-(loss+χdeep)≤((μ.sigma ν).prod κcoins).probability Prior:=by
    exact htri V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort θhost hθ hthreshold hdegree
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj ν κcoins E loss hE
  have hdegree':(1/2+α)*Fintype.card V≤D:=by
    have hn0:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith [mul_nonneg (show 0≤θhost-1/2 by linarith) hn0]
  exact hrows V U Γ Color P (permutationConflictGraph π (3*d)) D vsize hreg hn hdegree' hρlo hρhi (by omega) Q π hπ hnoshort le_rfl
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpR q hq hQ s hs hS j pH hj ν Prior (loss+χdeep) hprior
end Oberwolfach
