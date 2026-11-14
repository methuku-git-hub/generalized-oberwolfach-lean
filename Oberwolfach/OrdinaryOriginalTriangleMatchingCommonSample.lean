module

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
local instance (priority := 100000) originalTriangleMatchingCommonFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_original_triangle_matching_common_sample
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
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤κ→β≤δ→ξ+2*β<ηHub→
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
    1-εE≤(μ.sigma ν).probability E→
    1-(((((((εE+ζMatch)+χtwo)+χrows)+χdeep)+χcut)+χHub)+χEndpoint)-2/(Fintype.card (Fin n):ℝ)^q₀-
      (1/(Fintype.card (Fin n):ℝ)+2/(Fintype.card (Fin n):ℝ)^2)≤((μ.sigma ν).prod κcoins).probability
      (OrdinaryTriangleCommonSampleBundle P D vsize d β ε Q π hπ εR εH (2*p) rsv (θhost+α-β/2)
        κ αcut (ρ₀*smin) δcap βe βh b Bweight ηHub tpot s false weight m aK bK ξCorr EMatch) :=by
  have hpmin:0<ρ₀*smin:=by positivity
  have hpmin1:ρ₀*smin≤1:=by nlinarith [mul_nonneg hρ₀.le hsmin.le, mul_nonneg (by linarith : 0≤1-ρ₀) (by linarith : 0≤1-smin)]
  obtain ⟨Nmatch,hmatch⟩:=ordinary_original_regular_matching_core K d mMatch hd hmMatch ρ₀ BM tMatch ξMatch ζMatch smin
    hρ₀ hBM htMatch hξMatch hζMatch hsmin BO hBO
  obtain ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,htriangle⟩:=
    ordinary_triangle_matching_reservoir_two_step_named α ρ₀ (ρ₀*smin) cap hα hρ₀ hpmin hpmin1 hcap
  obtain ⟨δRes,hRes,εabs,εv,hδRes,hδRes1,hhRes,hεabs,hεv,htriangle⟩:=htriangle d hd
  refine ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,δRes,hRes,εabs,εv,hδRes,hδRes1,hhRes,hεabs,hεv,?_⟩
  intro ε χdeep χrows χcut hε hε1 hεκ hερ hεabs' hεv' hχdeep hχrows hχcut
    ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint hξ hχHub hηbal hζlimit htpot hχEndpoint hKdom hb hB buffer hbuffer
  obtain ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,htriangle⟩:=
    htriangle ε χdeep χrows χcut hε hε1 hεκ hερ hεabs' hεv' hχdeep hχrows hχcut
      ξ b Bweight ηHub Kdom χHub ηbal ζlimit tpot χEndpoint hξ hχHub hηbal hζlimit htpot hχEndpoint hKdom hb hB buffer hbuffer
  refine ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlim,hδ,hδα,hδcap,hδζ,hrate,htrace,?_⟩
  intro εR εH χtwo hεR hεH hχtwo β hβ hβ1 hβα hβκ hβδ hgap
  obtain ⟨v₀,hv₀,htriangle⟩:=htriangle εR εH χtwo hεR hεH hχtwo β hβ hβ1 hβα hβκ hβδ hgap
  refine ⟨v₀,hv₀,?_⟩
  intro vsize hvsize ξCorr hξCorr hξRes m
  obtain ⟨aK,bK,htriangle⟩:=htriangle vsize hvsize ξCorr hξCorr hξRes m
  refine ⟨aK,bK,?_⟩
  intro q₀
  obtain ⟨Ntriangle,hNtriangle,htriangle⟩:=htriangle q₀
  refine ⟨max Nmatch Ntriangle,by omega,?_⟩
  intro n U _ _ hn hn0 hUn F hF hK i₀ rsv θ cSample D hslo hs1 hθ hθ1 hcSample hda hρlo hρ1 hD
    Allowed hAllowed hsclass hclass
  have hn':max Nmatch Ntriangle≤n:=by simpa only [Fintype.card_fin] using hn
  obtain ⟨sampling,hmatch⟩:=hmatch n (by omega) hn0 U hUn F hF hK i₀ rsv θ cSample D
    hslo hs1 hθ hθ1 hcSample hda hρlo hρ1 hD Allowed hAllowed hsclass hclass
  refine ⟨sampling,?_⟩
  intro P hreg Q π hπ hnoshort θhost hθhost hθcycle hdegree τ A seed hseed w hw0 hwupper
  obtain ⟨weight,hweight,htriangle⟩:=htriangle n U P D hreg (by simpa using hn0) hρlo hρ1 (by omega)
    Q π hπ hnoshort θhost hθhost hθcycle (by simpa using hdegree)
  refine ⟨weight,hweight,?_⟩
  intro βe βh R _ ν E εE p p₂ q s μ wM wO EMatch κcoins αcut hE
  have hprior:=hmatch P hreg π θhost α hθhost hθcycle hα hdegree τ A seed hseed w hw0 hwupper hnoshort ν E εE hE
  have hpEq:2*p=initialIndexDensity U D*rsv:=by dsimp [p];ring
  have htriangle':=htriangle p 0 p₂ 0 sampling.u sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum
    rsv sampling.hpmin sampling.hsmin sampling.hrsv hpEq βe βh q sampling.hq sampling.hQ s sampling.hs sampling.hS false sampling.hfalse
    K mMatch (ordinaryEligibleHost P π d) wM wO tMatch ξMatch ν E (εE+ζMatch) hprior
  exact htriangle'
end Oberwolfach
