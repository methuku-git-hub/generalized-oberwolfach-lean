module

public import Oberwolfach.OrdinaryTriangleBufferedEndpointConstructedReservoirBundleCapped
public import Oberwolfach.OrdinaryVortexReservoirGeometry

@[expose] public section
/-! Specialize the combined triangle event to the actual first and terminal
vortex sets, deriving their reservoir geometry from the regular host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 80000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_vortex_buffered_constructed_reservoir_bundle_capped
    (α ρ₀ pmin cap:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1) (hcap:0<cap):
    ∃κ c C:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ 0<c ∧ 0<C ∧
    ∀(d:ℕ) (hd:2≤d),
    ∃δRes hRes εabs εv:ℝ,0<δRes ∧ δRes<1/4 ∧ 0<hRes ∧ 0<εabs ∧ 0<εv ∧
    ∀(ε χdeep χrows χcut:ℝ),
      0<ε→ε<1/4→ε≤κ→ε≤ρ₀/16→ε≤εabs→ε≤εv→0<χdeep→0<χrows→0<χcut→
    ∀(ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint:ℝ),
      0<ξ→0<χHub→0<ηbal→0<ζlimit→0<tpot→0<χEndpoint→1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*2+1))*Kdom^2≤Bweight→
    ∀(buffer:ℕ),2≤buffer→
    ∃t ζ δ δcap rate:ℝ,0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δ δcap rate d buffer ∧
    ∀(εR εH:ℝ),0<εR→0<εH→
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤κ→β≤δ→ξ+2*β<ηHub→
    ∃v₀:ℕ,1≤v₀ ∧ ∀vsize:ℕ,v₀≤vsize→
    ∀(ξCorr:ℝ),0<ξCorr→ξCorr≤hRes/100→∀m:ℕ,∃aK bK:ℕ,∀q₀:ℕ,∃N:ℕ,1≤N ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→N≤Fintype.card V→
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
      OrdinaryCorrectedProtectedReservoir 3 m (2*vsize) aK bK ξCorr (rawWheelGraph P raw\permutationConflictGraph π (3*d))
        (permutationConflictGraph π (3*d)) (rawWheelSpokes π d raw j)
        (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length)
        (Q.extendedIndices Q.length) (Q.extendedIndices 1)) := by
  obtain ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,hmain⟩:=ordinary_triangle_buffered_endpoint_constructed_reservoir_bundle_capped α ρ₀ pmin (ρ₀/4) cap hα hρ₀ hpmin hpmin1 (by positivity) hcap
  refine ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,?_⟩
  intro d hd
  obtain ⟨δRes,hRes,εabs,εv,hδRes,hδResSmall,hhRes,hεabs,hεv,hmain⟩:=hmain d hd
  refine ⟨δRes,hRes,εabs,εv,hδRes,hδResSmall,hhRes,hεabs,hεv,?_⟩
  intro ε χdeep χrows χcut hε hε1 hεκ hεsmall hεabs hεv hχdeep hχrows hχcut
    ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint hξ hχHub hηbal hζlimit htpot hχEndpoint hKdom hb hB buffer hbuffer
  obtain ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,hmain⟩:=
    hmain ε χdeep χrows χcut hε hε1 hεκ hεsmall hχdeep hχrows hχcut
      ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint hξ hχHub hηbal hζlimit htpot hχEndpoint hKdom hb hB buffer hbuffer
  refine ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,?_⟩
  intro εR εH hεR hεH β hβ hβ1 hβα hβκ hβδ hgap
  obtain ⟨v₀,hv₀,hmain⟩:=hmain εR εH hεR hεH β hβ hβ1 hβα hβκ hβδ hgap
  refine ⟨v₀,hv₀,?_⟩
  intro vsize hvsize ξCorr hξCorr hξRes m
  obtain ⟨aK,bK,hmain⟩:=hmain ξCorr hξCorr hξRes m
  refine ⟨aK,bK,?_⟩
  intro q₀
  obtain ⟨N,hN,hmain⟩:=hmain (2*vsize) (2*vsize) q₀
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D hreg hn hρlo hρhi hnN Q π hπ hnoshort θhost hθ hthreshold hdegree
  have hnreal:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  have hDlo:(Fintype.card V:ℝ)/2≤D:=by nlinarith
  have hD:0<D:=by
    have hh:0<(D:ℝ):=by nlinarith
    exact_mod_cast hh
  obtain ⟨hUlo,hUn,hA,hZ,hsize,hWW,hBB,hW,hB,hZsmall,hBsmall⟩:=
    ordinary_vortex_reservoir_geometry P D vsize β ε ρ₀ εabs εv Q hreg hn hD hDlo hρ₀ hρlo hρhi hε.le hεabs hεv
      (2*vsize) (2*vsize) (le_refl _) (le_refl _)
  obtain ⟨weight,hweight,hmain⟩:=hmain V U Γ Color P D vsize hreg hn hρlo hρhi hvsize hnN hUlo hUn hD Q π hπ hnoshort θhost hθ hthreshold hdegree
  refine ⟨weight,hweight,?_⟩
  intro p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq βe βh q hq hQ s hs hS j hj R _ ν E εE μ hE κcoins αcut
  have hout:=hmain p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq βe βh q hq hQ s hs hS j hj
    (Finset.univ\Q.extendedVertices 1) (Q.extendedVertices 1) (Q.extendedVertices Q.length) (Q.extendedVertices Q.length)
    (Q.extendedIndices Q.length) (Q.extendedIndices 1) hA hZ hsize hWW hBB hW hB hZsmall hBsmall ν E εE hE
  exact hout
end Oberwolfach
