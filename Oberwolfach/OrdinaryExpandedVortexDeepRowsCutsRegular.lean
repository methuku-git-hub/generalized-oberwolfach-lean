module

public import Oberwolfach.OrdinaryExpandedVortexDeepRowsRegular
public import Oberwolfach.OrdinaryExpandedFixedVortexRimCutsFromPrior

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_deep_rows_cuts_regular
    (mDeep:ℕ) (hm:3≤mDeep) (α ρ₀ pmin:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1):
    ∃K:ℕ,0<K ∧ ∃a ε₀ ρ θdeep:ℝ,0<a ∧ 0<ε₀ ∧ 0<ρ ∧ 0<θdeep ∧
    ∀(ε χdeep:ℝ),0<ε→ε<1/4→ε≤a→ε≤ρ₀/16→0<χdeep→
    ∀(β:ℝ),0≤β→β≤1/4→β≤α/8→β≤ε₀→
    ∀(εR εH χrows χcut:ℝ),0<εR→0<εH→0<χrows→0<χcut→
    ∀aLoad:ℝ,0<aLoad→aLoad≤a→∀d:ℕ,∀hd:2≤d,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold (mDeep+1)≤θhost→
      (θhost+α)*Fintype.card V≤D→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    let κcoins:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    let αcut:=min (α/4) (1/4:ℝ);
    1-(((εE+χrows)+χdeep)+χcut)≤((μ.sigma ν).prod κcoins).probability (fun z=>
      ((E z.1 ∧ OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D vsize β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryFixedVortexDeepCoverEvent mDeep K d a aLoad ρ θdeep P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin):=by
  obtain ⟨K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,hmain⟩:=
    ordinary_expanded_vortex_deep_rows_regular mDeep hm α ρ₀ pmin hα hρ₀ hpmin hpmin1
  refine ⟨K,hK,a,ε₀,ρ,θdeep,ha,hε₀,hρ,hθ,?_⟩
  intro ε χdeep hε hε1 hεa hεsmall hχdeep β hβ hβ1 hβα hβε εR εH χrows χcut hεR hεH hχrows hχcut
    aLoad hload hloadA d hd
  obtain ⟨vDeep,hvDeep,hdeep⟩:=hmain ε χdeep hε hε1 hεa hεsmall hχdeep β hβ hβ1 hβα hβε
    εR εH χrows hεR hεH hχrows aLoad hload hloadA d hd
  let αcut:ℝ:=min (α/4) (1/4:ℝ)
  have hαcut:0<αcut:=lt_min (by positivity) (by norm_num)
  have hαcut1:αcut≤1/2:=(min_le_right _ _).trans (by norm_num)
  have hαcutα:αcut≤α/2:=(min_le_left _ _).trans (by linarith)
  obtain ⟨vCuts,hvCuts,hcuts⟩:=ordinary_expanded_fixed_vortex_rim_cuts_from_prior α αcut pmin β ε ρ₀ χcut
    hα hαcut hαcut1 hαcutα hpmin hβ hβα hβ1 hε hε1 hρ₀ hχcut
  refine ⟨max vDeep vCuts,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpRlo hpHlo hpH1 hpEq q hq hQ s hs hS j hj R _ ν E εE μ hE κcoins αcut'
  have hDmargin:(1/2+α)*Fintype.card V≤D:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2+α:ℝ)≤θhost+α by linarith)
      (show (0:ℝ)≤Fintype.card V by positivity)
    exact hh.trans hdegree
  let Prior:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop:=fun z=>
    (E z ∧ OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D vsize β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) ∧
    OrdinaryFixedVortexDeepCoverEvent mDeep K d a aLoad ρ θdeep P D vsize β ε Q π hπ j
      (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))
  have hPrior:1-((εE+χrows)+χdeep)≤(μ.sigma ν).probability Prior:=by
    exact hdeep V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort θhost hθ hthreshold hdegree
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpRlo hpHlo hpH1 hpEq q hq hQ s hs hS j hj ν E εE hE
  exact hcuts V U Γ Color P D vsize hreg hn hDmargin hρlo hρhi (by omega) Q
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum hpRlo d hd q hq hQ s hs hS ν Prior ((εE+χrows)+χdeep) hPrior
end Oberwolfach
