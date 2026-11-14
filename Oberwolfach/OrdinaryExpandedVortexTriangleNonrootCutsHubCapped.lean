module

public import Oberwolfach.OrdinaryExpandedVortexTriangleNonrootRowsCutsCapped
public import Oberwolfach.OrdinaryExpandedVortexHubTraceCapBundleBounded

@[expose] public section
/-! Robust deep cover, row and index tests, oriented rim cuts, and adaptive
hub weights hold on the same expanded sample with one fixed trace cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_triangle_nonroot_cuts_hub_bundle_capped
    (α ρ₀ pmin cap:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1) (hcap:0<cap):
    ∃κ c C:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ 0<c ∧ 0<C ∧
    ∀(ε χdeep χrows χcut:ℝ),
      0<ε→ε<1/4→ε≤κ→ε≤ρ₀/16→0<χdeep→0<χrows→0<χcut→
    ∀(d:ℕ) (hd:2≤d) (ξ b Bweight ηHub Kdom χHub ηbal ζlimit:ℝ),
      0<ξ→0<χHub→0<ηbal→0<ζlimit→1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*2+1))*Kdom^2≤Bweight→
    ∃t ζ δ δcap rate:ℝ,0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δ δcap rate d ∧
    ∀(εR εH:ℝ),0<εR→0<εH→
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤κ→β≤δ→ξ+2*β<ηHub→
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold 3≤θhost→(θhost+α)*Fintype.card V≤D→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),
      pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(βe βh:ℝ),
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
    1-(((εE+χrows)+χdeep)+χcut)-χHub≤((μ.sigma ν).prod κcoins).probability (fun z=>
      (((E z.1 ∧ OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
        D vsize β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      OrdinaryFixedVortexTriangleNonrootCoverEvent d κ P D vsize β ε Q π hπ j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      (∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
        (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin)) ∧
      ∀i,i<Q.length→OrdinaryAdaptiveHubWeightsLevelEvent 2 (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        (2*p) pH (θhost+α-β/2) (εR*(markedVortexInnerVertices Q i).card) (εH*(markedVortexInnerHubs Q i).card)
        (2*((3*d:ℕ):ℝ)+δcap*min ((markedVortexInnerVertices Q i).card:ℝ) (markedVortexInnerHubs Q i).card)
        βe βh b Bweight ηHub (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))) :=by
  obtain ⟨κ,hκ,hκ1,hκcap,hdeep⟩:=
    ordinary_expanded_vortex_triangle_nonroot_rows_cuts_capped α ρ₀ pmin cap hα hρ₀ hpmin hpmin1 hcap
  obtain ⟨c,C,hc,hC,hhub⟩:=ordinary_expanded_vortex_hub_trace_cap_bundle_bounded 2 (by omega) α hα
  refine ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,?_⟩
  intro ε χdeep χrows χcut hε hε1 hεa hεsmall hχdeep hχrows hχcut
    d hd ξ b Bweight ηHub Kdom χHub ηbal ζlimit hξ hχHub hηbal hζlimit hKdom hb hB
  obtain ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,hhub⟩:=
    hhub d hd ε ρ₀ pmin ξ b Bweight ηHub Kdom χHub ηbal ζlimit hε hε1 hρ₀ hpmin hpmin1 hξ hχHub hηbal hζlimit hKdom hb hB
  refine ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,?_⟩
  intro εR εH hεR hεH β hβ hβ1 hβα hβε hβδ hgap
  obtain ⟨vDeep,hvDeep,hdeep⟩:=hdeep ε χdeep hε hε1 hεa hεsmall hχdeep β hβ hβ1 hβα hβε
    εR εH χrows χcut hεR hεH hχrows hχcut d hd
  obtain ⟨vHub,hvHub,hhub⟩:=hhub β hβ hβ1 hβα hβδ hgap
  refine ⟨max vDeep vHub,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq βe βh q hq hQ s hs hS j hj R _ ν E εE μ hE κcoins αcut
  let Prior:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop:=fun z=>
    ((E z.1 ∧ OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d))
      D vsize β ε Q π hπ (2*p) pH s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
    OrdinaryFixedVortexTriangleNonrootCoverEvent d κ P D vsize β ε Q π hπ j
      (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
    ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
      (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin
  have hPrior:1-(((εE+χrows)+χdeep)+χcut)≤((μ.sigma ν).prod κcoins).probability Prior:=by
    exact hdeep V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort θhost hθ hthreshold hdegree
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj ν E εE hE
  exact hhub V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort θhost hθ hthreshold hdegree
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq
    (fun _=>θhost+α-β/2) (fun i=>εR*(markedVortexInnerVertices Q i).card)
    (fun i=>εH*(markedVortexInnerHubs Q i).card) (fun _=>βe) (fun _=>βh)
    q hq hQ s hs hS j ν κcoins Prior (((εE+χrows)+χdeep)+χcut) hPrior
end Oberwolfach
