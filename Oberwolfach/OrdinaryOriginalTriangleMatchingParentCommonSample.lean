module

public import Oberwolfach.OrdinaryOriginalTriangleMatchingCommonSample
public import Oberwolfach.OrdinaryTriangleCommonBundleParentSupported
public import Oberwolfach.OrdinaryTriangleParentHostBounds
public import Oberwolfach.OrdinaryShiftedMatchingWithPrior
public import Oberwolfach.OrdinaryOriginalRegularMatchingCore
public import Oberwolfach.OrdinaryTriangleMatchingReservoirTwoStepNamed

@[expose] public section
/-! Select the assigned law from the factor hypotheses, prove its matching
core likely, and attach the triangle correction and level tests to that same
expanded outcome and the same reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := 100000) originalTriangleMatchingParentCommonFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_original_triangle_matching_parent_common_sample
    (K d mMatch:ℕ) (hd:2≤d) (hmMatch:3≤mMatch)
    (α ρ₀ smin cap BM tMatch ξMatch ζMatch:ℝ)
    (hα:0<α) (hρ₀:0<ρ₀) (hρ₀1:ρ₀≤1) (hsmin:0<smin) (hsmin1:smin≤1)
    (hcap:0<cap) (hBM:0<BM) (htMatch:0<tMatch) (hξMatch:0<ξMatch) (hζMatch:0<ζMatch)
    (BO:Fin K→ℝ) (hBO:∀i,0<BO i):
    ∃κ c C:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ 0<c ∧ 0<C ∧
    ∃δRes hRes εabs εv:ℝ,0<δRes ∧ δRes<1/4 ∧ 0<hRes ∧ 0<εabs ∧ 0<εv ∧
    ∀(ε χdeep χrows χcut:ℝ),
      0<ε→ε<1/4→ε≤κ→ε≤ρ₀/16→ε≤εabs→ε≤εv→0<χdeep→0<χrows→0<χcut→
    ∀(ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint:ℝ),
      0<ξ→0<χHub→0<ηbal→0<ζlimit→0<tpot→0<χEndpoint→1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/(ρ₀*smin)^(3*2+1))*Kdom^2≤Bweight→
    ∀(buffer:ℕ),2≤buffer→
    ∃t ζ δ δcap rate:ℝ,0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ α (ρ₀*smin) (ρ₀*smin) ηbal ζ δ δcap rate d buffer ∧
    ∀(εR εH χtwo:ℝ),0<εR→0<εH→0<χtwo→
    ∀(kParent Mhost Mcut:ℕ) (βP ηP ηParent βH cParent Bparent εTri χhost δref href χref:ℝ)
      (hselector:OrdinaryTriangleFixedDomainSelector kParent d Mhost hd (max (1/2) (cycleThreshold 3)) (α/2) (ρ₀*smin)
        (ρ₀/16) βP ηP ηParent βH cParent Bparent εTri ε χhost (2*(3*d)) (by positivity))
      (hcuts:OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) (ρ₀*smin) (ρ₀/16) δref href ε χref (2*(3*d))),
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤εTri→β≤κ→β≤δ→ξ+2*β<ηHub→
    ∃v₀:ℕ,1≤v₀ ∧ ∀vsize:ℕ,v₀≤vsize→
    ∀(ξCorr:ℝ),0<ξCorr→ξCorr≤hRes/100→∀m:ℕ,∃aK bK:ℕ,∀q₀:ℕ,∃N:ℕ,1≤N ∧
    ∀(n:ℕ) (U:Type) [Fintype U] [LinearOrder U],N≤Fintype.card (Fin n)→0<n→Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hK:0<K) (i₀:Fin K) (rsv θ cSample:ℝ) (D:ℕ)
      (hslo:smin≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hcSample:8≤cSample)
      (hda:1/θ≤d) (hρlo:ρ₀≤ initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1) (hD:0<D)
      (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀u,factorPreparationClass (F u) K=some i₀),
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ cSample ρ₀ smin d,
    ∀(P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (Q:Vortex U P D β ε vsize) (π:Equiv.Perm (Fin n))
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
      (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
      (θhost:ℝ) (hθhost:1/2≤θhost) (hθcycle:cycleThreshold 3≤θhost) (hdegree:(θhost+α)*n≤D)
      (τ A:ℝ) (seed:(Fin (mMatch+1)→Fin n)→ℝ)
      (hseed:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM seed)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (hw0:∀i C,0≤w i C) (hwupper:∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)),
    ∃weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
      (∀i,i<Q.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (weight i)) ∧
    let L:=Q.length-1;let W:=markedVortexVertexType Q;let Z:=markedVortexHubType Q;
    let f:=fun i=>(markedVortexVertexEmbedding Q i).toEmbedding;let g:=fun i=>markedVortexHubEmbedding Q i;
    let ρi:=markedVortexPermutation Q π hπ;let Conflict:=permutationConflictGraph π (3*d);
    ∃selection:OrdinaryTriangleFullDomainSelection kParent d hd (max (1/2) (cycleThreshold 3)) (α/2) (ρ₀*smin)
      (ρ₀/16) βP ηP ηParent βH cParent Bparent εTri χhost (2*(3*d)) (by positivity)
      (Fin n) U Bool Bool W Z P Conflict f g ρi L,
    ∀(βe βh:ℝ)
      {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ cSample D
    let q:=ordinaryAssignedMarkedProbability F hF K θ cSample
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ cSample
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ cSample D π d mMatch seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ cSample D (ordinaryEligibleHost P π d) π d w
    let EMatch:=OrdinaryShiftedMatchingWithPrior (ordinaryEligibleHost P π d) π d mMatch K p₂ 0 q s wM wO tMatch ξMatch E
    let κcoins:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin)
    let αcut:=min (α/4) (1/4:ℝ);
    let Host:RawWheelOutcome (Fin n) U Bool Bool→Prop:=fun raw=>∀i≤L,
      ordinaryCombinedTriangleEvent d kParent (P.comap (f i)) (Conflict.comap (f i)) (ρi i)
        (max (1/2) (cycleThreshold 3)) (α/2) (ρ₀*smin) βP ηP ηParent βH cParent Bparent (2*p) rsv
        (selection.weight i) false (ordinaryRawRestrictPair (f i) (g i) raw)
    let Cuts:RawWheelOutcome (Fin n) U Bool Bool×(Sym2 (Fin n)→Bool)→Prop:=fun z=>∀i≤L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (f i)) (Conflict.comap (f i)) (ρi i) d false δref href
        (ordinaryRawRestrictPair (f i) (g i) z.1) (fun e=>z.2 (Sym2.map (f i) e))
    let Good:=OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH (2*p) rsv (θhost+α-β/2)
      κ αcut (ρ₀*smin) δcap βe βh b Bweight ηHub tpot s false weight m aK bK ξCorr EMatch
    let All:=fun z=>Good z ∧ Host (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      Cuts ((fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)),z.2)
    let loss:ℝ:=(((((((εE+ζMatch)+χtwo)+χrows)+χdeep)+χcut)+χHub)+χEndpoint)+
      2/(Fintype.card (Fin n):ℝ)^q₀+(1/(Fintype.card (Fin n):ℝ)+2/(Fintype.card (Fin n):ℝ)^2);
    1-εE≤(μ.sigma ν).probability E→
    1-loss-χhost-χref≤((μ.sigma ν).prod κcoins).probability All ∧
      (0<1-loss-χhost-χref→∃z,0<((μ.sigma ν).prod κcoins).mass z ∧ All z) :=by
  have hpmin:0<ρ₀*smin:=by positivity
  obtain ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,δRes,hRes,εabs,εv,hδRes,hδRes1,hhRes,hεabs,hεv,hcommon⟩:=
    ordinary_original_triangle_matching_common_sample K d mMatch hd hmMatch α ρ₀ smin cap BM tMatch ξMatch ζMatch
      hα hρ₀ hρ₀1 hsmin hsmin1 hcap hBM htMatch hξMatch hζMatch BO hBO
  refine ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,δRes,hRes,εabs,εv,hδRes,hδRes1,hhRes,hεabs,hεv,?_⟩
  intro ε χdeep χrows χcut hε hε1 hεκ hερ hεabs' hεv' hχdeep hχrows hχcut
    ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint hξ hχHub hηbal hζlimit htpot hχEndpoint hKdom hb hB buffer hbuffer
  obtain ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,hcommon⟩:=
    hcommon ε χdeep χrows χcut hε hε1 hεκ hερ hεabs' hεv' hχdeep hχrows hχcut
      ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint hξ hχHub hηbal hζlimit htpot hχEndpoint hKdom hb hB buffer hbuffer
  refine ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,?_⟩
  intro εR εH χtwo hεR hεH hχtwo kParent Mhost Mcut βP ηP ηParent βH cParent Bparent εTri χhost δref href χref hselector hcuts
    β hβ hβ1 hβα hβε hβκ hβδ hgap
  obtain ⟨v₀,hv₀,hcommon⟩:=hcommon εR εH χtwo hεR hεH hχtwo β hβ hβ1 hβα hβκ hβδ hgap
  obtain ⟨vparent,hvparent,hparentSize⟩:=ordinary_vortex_parent_terminal_thresholds ε hε Mhost Mcut
  refine ⟨max v₀ vparent,by omega,?_⟩
  intro vsize hvsize ξCorr hξCorr hξRes m
  obtain ⟨aK,bK,hcommon⟩:=hcommon vsize (by omega) ξCorr hξCorr hξRes m
  refine ⟨aK,bK,?_⟩
  intro q₀
  obtain ⟨N,hN,hcommon⟩:=hcommon q₀
  refine ⟨N,hN,?_⟩
  intro n U _ _ hn hn0 hUn F hF hK i₀ rsv θ cSample D hslo hs1 hθ hθ1 hcSample hda hρlo hρ1 hD
    Allowed hAllowed hsclass hclass
  obtain ⟨sampling,hcommon⟩:=hcommon n U hn hn0 hUn F hF hK i₀ rsv θ cSample D
    hslo hs1 hθ hθ1 hcSample hda hρlo hρ1 hD Allowed hAllowed hsclass hclass
  refine ⟨sampling,?_⟩
  intro P hreg Q π hπ hnoshort θhost hθhost hθcycle hdegree τ A seed hseed w hw0 hwupper
  obtain ⟨weight,hweight,hcommon⟩:=hcommon P hreg Q π hπ hnoshort θhost hθhost hθcycle hdegree τ A seed hseed w hw0 hwupper
  refine ⟨weight,hweight,?_⟩
  intro L W Z f g ρi Conflict
  let p:=initialIndexDensity U D*rsv/2
  let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ cSample D
  have hpEq:2*p=initialIndexDensity U D*rsv:=by dsimp [p];ring
  have hL:L<Q.length:=by dsimp [L];have hh:=Q.length_pos;omega
  have hsize:=hparentSize vsize (by omega)
  obtain ⟨selection,hparent⟩:=ordinary_triangle_common_bundle_parent_supported kParent d Mhost Mcut hd
    α ρ₀ (ρ₀*smin) βP ηP ηParent βH cParent Bparent εTri ε χhost δref href χref hpmin hselector hcuts
    n U P D vsize β Q π hπ hreg (by simpa using hn0) hα θhost hθhost hθcycle (by simpa using hdegree)
    hρ₀ hρlo hρ1 hβ hβα hβ1 hβε hε (by linarith) hερ (by omega) hnoshort
    p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    rsv sampling.hpmin sampling.hsmin sampling.hrsv hpEq L hL hsize.1 hsize.2
  refine ⟨selection,?_⟩
  intro βe βh R _ ν E εE p' p₂' q s μ wM wO EMatch κcoins αcut Host Cuts Good All loss hE
  have hgood:=hcommon βe βh ν E εE hE
  have hgood':1-loss≤((μ.sigma ν).prod κcoins).probability Good:=by dsimp [loss];linarith only [hgood]
  exact hparent q sampling.hq sampling.hQ s sampling.hs sampling.hS false sampling.hfalse
    εR εH (θhost+α-β/2) κ αcut (ρ₀*smin) δcap βe βh b Bweight ηHub tpot weight m aK bK ξCorr
    ν EMatch loss hgood'
end Oberwolfach
