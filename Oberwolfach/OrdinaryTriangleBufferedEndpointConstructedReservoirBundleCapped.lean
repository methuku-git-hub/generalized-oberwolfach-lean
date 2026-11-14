module

public import Oberwolfach.OrdinaryExpandedVortexTriangleBufferedNonrootCutsHubEndpointCapped
public import Oberwolfach.OrdinarySameSampleConstructedReservoirEarlyGeometry
public import Oberwolfach.PermutationConflictDegree

@[expose] public section
/-! Choose the triangle common tests, endpoint weights and protected
reservoir/correction on the same expanded sample and direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_buffered_endpoint_constructed_reservoir_bundle_capped
    (α ρ₀ pmin ω cap:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1) (hω:0<ω) (hcap:0<cap):
    ∃κ c C:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ 0<c ∧ 0<C ∧
    ∀(d:ℕ) (hd:2≤d),
    ∃δRes hRes εabs εv:ℝ,0<δRes ∧ δRes<1/4 ∧ 0<hRes ∧ 0<εabs ∧ 0<εv ∧
    ∀(ε χdeep χrows χcut:ℝ),
      0<ε→ε<1/4→ε≤κ→ε≤ρ₀/16→0<χdeep→0<χrows→0<χcut→
    ∀(ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint:ℝ),
      0<ξ→0<χHub→0<ηbal→0<ζlimit→0<tpot→0<χEndpoint→1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*2+1))*Kdom^2≤Bweight→
    ∀(buffer:ℕ),2≤buffer→
    ∃t ζ δ δcap rate:ℝ,0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δ δcap rate d buffer ∧
    ∀(εR εH:ℝ),0<εR→0<εH→
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤κ→β≤δ→ξ+2*β<ηHub→
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(ξCorr:ℝ),0<ξCorr→ξCorr≤hRes/100→∀m:ℕ,∃aK bK:ℕ,∀tK fK q₀:ℕ,∃N:ℕ,1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→N≤Fintype.card V→
      ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→0<D→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold 3≤θhost→(θhost+α)*Fintype.card V≤D→
    ∃weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
      (∀i,i<Q.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (weight i)) ∧
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),
      pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(βe βh:ℝ),
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (hj:∀w,s w j=pH),
    ∀(A Z Wterm W:Finset V) (Bterm B:Finset U),
      A=Finset.univ\Z→(Z.card:ℝ)≤εabs*Fintype.card V→
      Wterm.card+Bterm.card≤tK→Wterm⊆W→Bterm⊆B→W.card≤fK→
      (B.card:ℝ)≤εabs*Fintype.card V+fK→
      (Z.card:ℝ)≤εv*Fintype.card V→(B.card:ℝ)≤εv*Fintype.card V+fK→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    let κcoins:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    let αcut:=min (α/4) (1/4:ℝ);
    1-(((((εE+χrows)+χdeep)+χcut)+χHub)+χEndpoint)-2/(Fintype.card V:ℝ)^q₀-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)≤((μ.sigma ν).prod κcoins).probability (fun z=>((
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
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))) ∧
      ∀i,i<Q.length→EndpointPhysicalPotentialEvent
        (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
        (markedVortexPermutation Q π hπ i) d j (weight i) (2*p) pH tpot
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))) ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir 3 m tK aK bK ξCorr (rawWheelGraph P raw\permutationConflictGraph π (3*d))
        (permutationConflictGraph π (3*d)) (rawWheelSpokes π d raw j) A Z Wterm Bterm B) := by
  obtain ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,hcommon⟩:=ordinary_expanded_vortex_triangle_buffered_nonroot_cuts_hub_endpoint_capped α ρ₀ pmin cap hα hρ₀ hpmin hpmin1 hcap
  refine ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,?_⟩
  intro d hd
  obtain ⟨δRes,hRes,εabs,εv,hδRes,hδResSmall,hhRes,hεabs,hεv,hreservoir⟩:=
    ordinary_same_sample_constructed_reservoir_probability_early_geometry 3 d (by omega) hd α pmin ω
      (2*((3*d:ℕ):ℝ)) hα hpmin hpmin1 hω (by positivity)
  refine ⟨δRes,hRes,εabs,εv,hδRes,hδResSmall,hhRes,hεabs,hεv,?_⟩
  intro ε χdeep χrows χcut hε hε1 hεκ hεsmall hχdeep hχrows hχcut
    ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint hξ hχHub hηbal hζlimit htpot hχEndpoint hKdom hb hB buffer hbuffer
  obtain ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,hcommon⟩:=
    hcommon ε χdeep χrows χcut hε hε1 hεκ hεsmall hχdeep hχrows hχcut
      d hd ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint hξ hχHub hηbal hζlimit htpot hχEndpoint hKdom hb hB buffer hbuffer
  refine ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,?_⟩
  intro εR εH hεR hεH β hβ hβ1 hβα hβκ hβδ hgap
  obtain ⟨v₀,hv₀,hcommon⟩:=hcommon εR εH hεR hεH β hβ hβ1 hβα hβκ hβδ hgap
  refine ⟨v₀,hv₀,?_⟩
  intro ξCorr hξCorr hξRes m
  obtain ⟨aK,bK,hreservoir⟩:=hreservoir ξCorr hξCorr hξRes m
  refine ⟨aK,bK,?_⟩
  intro tK fK q₀
  obtain ⟨N,hN,hreservoir⟩:=hreservoir tK fK q₀
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv hnN hωU hUn hD Q π hπ hnoshort θhost hθ hthreshold hdegree
  obtain ⟨weight,hweight,hcommon⟩:=hcommon V U Γ Color P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
  refine ⟨weight,hweight,?_⟩
  intro p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq βe βh q hq hQ s hs hS j hj
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall R _ ν E εE μ hE κcoins αcut
  let Common:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop:=fun z=>
(
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
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))) ∧
      ∀i,i<Q.length→EndpointPhysicalPotentialEvent
        (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
        (markedVortexPermutation Q π hπ i) d j (weight i) (2*p) pH tpot
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))
  have hCommon:1-(((((εE+χrows)+χdeep)+χcut)+χHub)+χEndpoint)≤((μ.sigma ν).prod κcoins).probability Common:=by
    have hh:=hcommon p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq βe βh q hq hQ s hs hS j hj ν E εE hE
    linarith
  have hF:∀v,((permutationConflictGraph π (3*d)).degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro v
    have hh:=permutationConflictGraph_degree_le π (3*d) v
    exact_mod_cast hh
  have hdegree':(cycleThreshold 3+α)*Fintype.card V≤D:=by
    have hn0:0≤(Fintype.card V:ℝ):=by positivity
    nlinarith
  have hout:=hreservoir V U Γ Color hnN hωU hUn P (permutationConflictGraph π (3*d)) D hreg hD hdegree' hF
    π (le_refl _) hnoshort p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall ν Common
    (((((εE+χrows)+χdeep)+χcut)+χHub)+χEndpoint) hCommon
  exact hout
end Oberwolfach
