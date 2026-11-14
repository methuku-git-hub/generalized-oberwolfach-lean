module

public import Oberwolfach.MarkedConstructedReferenceStateStepUniform
public import Oberwolfach.MarkedReferenceLevelData
public import Oberwolfach.MarkedReferenceStateStepDecomposition
public import Oberwolfach.MarkedReferenceDeletionState
public import Oberwolfach.MarkedNextSampleCanonicalRemainder
public import Oberwolfach.MarkedDeletedCoverFixedRemainder
public import Oberwolfach.MarkedReferenceInputStability
public import Oberwolfach.MarkedGlobalCoverInputMargins
public import Oberwolfach.MarkedLocalCoverInputMargins
public import Oberwolfach.MarkedNestedIterationBalanceInputs
public import Oberwolfach.MarkedResourceDomainMonotonicity
public import Oberwolfach.MarkedIterationNeighbourhoodFromResources
public import Oberwolfach.MarkedIterationToleranceChoices

@[expose] public section

/-! Apply protected cover-down to the actual finite deletion of a fixed
reference. All analytic estimates of the current sample are derived from
those of the reference and the displayed global and star allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_uniform_reference_level_constructor_uniform_densities (gamma pA0:ℝ)
    (hg:0< gamma) (hg1:gamma≤   1) (hpA0:0< pA0) (hpA01:pA0≤   1/2):
    ∃ c₀:ℕ,∀ r:ℕ,2≤r→c₀≤r+5→∀ rho₀ omega₀ t₀ p0 betaA aLoA BA:ℝ,
    0<rho₀ → rho₀≤1 → 0<omega₀ → 0<t₀ → t₀≤1 → 0<p0 → p0≤1/2 → 0<betaA → 0<aLoA → 0<BA →
    ∃ Kgeom:ℕ,0< Kgeom∧   ∃ kappa0 ξ thetaDeep:ℝ,0< kappa0∧   0<ξ∧   0< thetaDeep∧   ∀ kappa:ℝ,0< kappa →            kappa≤   kappa0 →            
    ∀ alphaInner omegaInner:ℝ,0< alphaInner →         0< omegaInner →         omegaInner≤   1 →         
    ∃ betaExt epsilonExt:ℝ,0< betaExt∧   0< epsilonExt∧   
    ∃ gammaMax:ℝ,0<gammaMax ∧ ∀ gammaLoss iota β aLo B:ℝ,0<gammaLoss → gammaLoss≤gammaMax →   0< iota →        0<β →        β≤   betaExt →        0< aLo →        0≤   B →        
    ∃ η ηEnd ζ ζD pmax:ℝ,0<η∧   0<ηEnd∧   0<ζ∧   0<ζD∧   0< pmax∧   pmax≤   1/8∧   
    ∀ (p:ℝ) (hp:0< p) (hp1:p≤   1),p≤   pmax →            ∃ θ:ℝ,0<θ∧   
    ∃ delta:ℝ,0< delta∧   ∀ x:ℝ,0< x →    x≤   delta →    
    ∃ sigmaMax:ℝ,0<sigmaMax ∧ ∀ sigmaLoss:ℝ,0<sigmaLoss → sigmaLoss≤sigmaMax →  ∀ omegaI hIcut deltaI:ℝ,0< omegaI →    0< hIcut →    0< deltaI →    deltaI<1/4 →    
    ∃ etaBal:ℝ,0< etaBal∧   ∃ NI:ℕ,∀ d:ℕ,1≤   d →            ∃ N:ℕ,1≤   N∧   
    ∀ rho omega t:ℝ,rho₀≤rho → rho≤1 → omega₀≤omega → omega≤1 → t₀≤t → (r+4:ℝ)*t≤1 →
    pA0≤rho*(r+4:ℝ)*t/2 → p0≤rho*(r+4:ℝ)*t/2 → p0≤rho*t/2 → p0≤t →
    ∀ (Gamma Color : Type) [Fintype Gamma] [Fintype Color],
    ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom gamma rho omega t p0 betaA aLoA BA kappa ξ thetaDeep alphaInner omegaInner iota β aLo B η x omegaI hIcut deltaI etaBal,
    let VP:=level.VP
    let UP:=level.UP
    let W:=level.W
    let V:=level.V
    let U:=level.U
    letI : Fintype VP := level.inst7
    letI : Fintype UP := level.inst8
    letI : LinearOrder VP := level.inst9
    letI : DecidableEq UP := level.inst10
    letI : Fintype W := level.inst11
    letI : LinearOrder W := level.inst12
    letI : Fintype V := level.inst13
    letI : LinearOrder V := level.inst14
    letI : Fintype U := level.inst15
    letI : DecidableEq U := level.inst16
    let fA:=level.fA
    let gA:=level.gA
    let PP:=level.PP
    let πP:=level.πP
    let π:=level.π
    let T:=level.T
    let Wrem:=level.Wrem
    let qP:=level.qP
    let sP:=level.sP
    let aP:=level.aP
    let cP:=level.cP
    let σBase:=level.σBase
    let HBase:=level.HBase
    let I:=level.I
    let J:=level.J
    let tauRef:=level.tauRef
    let weightRef:=level.weightRef
    let xiDeep:=level.xiDeep
    let f:=level.f
    let ρ:=level.ρ
    let D:=level.D
    let τweight:=level.τweight
    let weight:=level.weight
    let Zinner:=level.Zinner
    let errR0:=level.errR0
    let errI0:=level.errI0
    let errParent:=level.errParent
    let errInner:=level.errInner
    let errDeep:=level.errDeep
    let EBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) false
    let KBase:=MarkedSampleArc PP πP (3*d) (fun e=>σBase (Sum.inl e)) true
    let SBase:=Finset.univ.filter (fun z:VP×UP=>HBase false z.1 z.2∨HBase true z.1 z.2);
    ∀ CState:MarkedReferenceDeletion PP πP d σBase,
    CState.Valid HBase (r+4) I J (gammaLoss*Fintype.card VP) (sigmaLoss*Fintype.card VP) →
    let KA:=CState.arcs
    let KS:=CState.spokes;
    ∃ N:Finset (MarkedWheel (fun e:EBase=>e.val.1) (fun e=>e.val.2)
      (fun e:KBase=>e.val.1) (fun e=>e.val.2) (r+4) πP (3*d) (HBase false) (HBase true)),
      (∀ Y∈N,∀ Z∈N,Y≠Z → Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z)) ∧
      N.biUnion markedWheelArcs⊆Finset.univ\KA ∧ N.biUnion markedWheelSpokePairs⊆SBase\KS ∧
      let AR:=Finset.univ\(KA∪N.biUnion markedWheelArcs)
      let SR:=SBase\(KS∪N.biUnion markedWheelSpokePairs)
      let BBase:=markedFiniteResources (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP Finset.univ SBase
      let L:=markedFiniteResources (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP AR SR;
      HasResourceDecomposition
        (fun W:MarkedWheel (fun e:EBase=>e.val.1) (fun e=>e.val.2)
          (fun e:KBase=>e.val.1) (fun e=>e.val.2) (r+4) πP (3*d) (HBase false) (HBase true)=>markedWheelPhysicalResources W)
        (CState.remaining HBase\L) ∧
      MarkedRemainderDivisible (fun e:EBase=>e.val.1) (fun e=>e.val.2)
        (fun e:KBase=>e.val.1) (fun e=>e.val.2) (HBase true) AR SR (r+4) ∧
      (∀ a∈AR,Sum.elim (fun e:EBase=>e.val.1) (fun e:KBase=>e.val.1) a∈I ∧
        Sum.elim (fun e:EBase=>e.val.2) (fun e:KBase=>e.val.2) a∈I) ∧
      (∀ z∈SR,z.1∈I∧z.2∈J) ∧
      ∃ F⊆BBase.filter (markedInnerResource I J),
        L=BBase.filter (markedInnerResource I J)\F ∧
        F.filter (markedInnerResource T Wrem)=∅ ∧
        (∀ physical z,(((markedIncidentEdges (fun e:EBase=>e.val.1) (fun e=>e.val.2)
          (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) physical z).filter
          (fun e=>markedActivePhysical (fun e:EBase=>e.val.1) (fun e=>e.val.2)
            (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) e∈F)).card:ℝ)≤gammaLoss*I.card) ∧
        (∀ physical z,(((markedIncidentEdges (fun e:EBase=>e.val.1) (fun e=>e.val.2)
          (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) physical z).filter
          (fun e=>markedActivePhysical (fun e:EBase=>e.val.1) (fun e=>e.val.2)
            (fun e:KBase=>e.val.1) (fun e=>e.val.2) πP (HBase false) (HBase true) e∈F.filter (markedStarResource T Wrem))).card:ℝ)≤sigmaLoss*I.card) ∧
        ∀ (WNext ZNext:Type) [Fintype WNext] [Fintype ZNext] [LinearOrder WNext] [DecidableEq ZNext]
          (fNext:WNext↪oVP) (gNext:ZNext↪UP) (πNext:Equiv.Perm WNext),
          (∀ x,fNext (πNext x)=πP (fNext x)) →
          Finset.univ.image fNext=I → Finset.univ.image gNext=J →
          ∀ (XNext:Finset WNext) (YNext:Finset ZNext),
          (∀ x,fNext x∈T↔x∈XNext) → (∀ u,gNext u∈Wrem↔u∈YNext) →
    let σ₀:=rawMarkedRestrictPair fNext gNext σBase
    let H₀:=fun b x u=>HBase b (fNext x) (gNext u);
    ∃ Next:MarkedReferenceDeletion (PP.comap fNext) πNext d σ₀,
      Next.Valid H₀ (r+4) XNext YNext (gammaLoss*I.card) (sigmaLoss*I.card) ∧
      Next.removed.image (markedResourceEmbedding fNext.toEmbedding gNext)=F ∧
      (Next.remaining H₀).image (markedResourceEmbedding fNext.toEmbedding gNext)=L := by
  obtain ⟨c₀,hcover⟩ := marked_constructed_reference_state_step_uniform_densities gamma pA0 hg hg1 hpA0 hpA01
  refine ⟨c₀,?_⟩
  intro r hr hrc rho₀ omega₀ t₀ p0 betaA aLoA BA hrho₀ hrho₀1 ho₀ ht₀ ht₀1 hp0 hp01 hbA haA hBA
  obtain ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,hcover⟩ :=
    hcover r hr hrc rho₀ omega₀ t₀ p0 betaA aLoA BA hrho₀ hrho₀1 ho₀ ht₀ ht₀1 hp0 hp01 hbA haA hBA
  refine ⟨Kgeom,hKgeom,kappa0,ξ,thetaDeep,hkappa0,hξ,hΘDeep,?_⟩
  intro kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,hcover⟩ := hcover kappa hkappa hkk alphaInner omegaInner hAlpha hOmega hOmega1
  obtain ⟨gammaMax,hGammaMax,hcover⟩ := hcover
  refine ⟨betaExt,epsilonExt,hBetaExt,hEpsilonExt,gammaMax,hGammaMax,?_⟩
  intro gammaLoss iota β aLo B hGammaLoss hGammaBound hIota hβ hBetaSmall haLo hB
  obtain ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,hcover⟩ :=
    hcover gammaLoss iota β aLo B hGammaLoss hGammaBound hIota hβ hBetaSmall haLo hB
  refine ⟨η,ηEnd,ζ,ζD,pmax,hη,hηEnd,hζ,hζD,hpmax,hpmax8,?_⟩
  intro p hp hp1 hpp
  obtain ⟨θ,hθ,delta,hdelta,hcover⟩ := hcover p hp hp1 hpp
  refine ⟨θ,hθ,delta,hdelta,?_⟩
  intro x hx hxdelta
  obtain ⟨sigmaMax,hSigmaMax,hcover⟩ := hcover x hx hxdelta
  refine ⟨sigmaMax,hSigmaMax,?_⟩
  intro sigmaLoss hSigmaLoss hSigmaBound omegaI hIcut deltaI hoI hhI hdI hdIs
  obtain ⟨etaBal,hetaBal,NI,hcover⟩ := hcover sigmaLoss hSigmaLoss hSigmaBound omegaI hIcut deltaI hoI hhI hdI hdIs
  refine ⟨etaBal,hetaBal,NI,?_⟩
  intro d hd
  obtain ⟨NN,hNN,hcover⟩ := hcover d hd
  refine ⟨NN,hNN,?_⟩
  intro rho omega t hρ hrho1 hω ho1 htlo ht1 hPA0 hpr hpk hpt
  intro Gamma Color _ _ level
  letI : Fintype level.VP := level.inst7
  letI : Fintype level.UP := level.inst8
  letI : LinearOrder level.VP := level.inst9
  letI : DecidableEq level.UP := level.inst10
  letI : Fintype level.W := level.inst11
  letI : LinearOrder level.W := level.inst12
  letI : Fintype level.V := level.inst13
  letI : LinearOrder level.V := level.inst14
  letI : Fintype level.U := level.inst15
  letI : DecidableEq level.U := level.inst16
  dsimp only
  intro CState hState
  exact hcover rho omega t hρ hrho1 hω ho1 htlo ht1 hPA0 hpr hpk hpt
    level.VP level.UP level.W level.V level.U Gamma Color level.hnP
    level.hUP level.hUPlow level.hnW level.hWlow level.fA level.gA level.PP level.πP
    level.π level.hcomm level.T level.Wrem level.hT level.hfX level.hgX level.hTsize
    level.hWsize level.hPdeg level.hPreg level.qP level.sP level.aP level.cP level.hqP
    level.hsP level.σBase level.HBase level.I level.J CState hState level.hstats0
    level.hcuts0 level.hconfigsP0 level.hrowsP0 level.hindicesP0 level.hrowOld0 level.hcolOld0 level.hDloP level.hDhiP
    level.tauRef level.weightRef level.hwRef level.hloadRef0 level.hDeepConfigs0 level.hDeepLoad0 level.xiDeep level.hXi0
    level.hXiScale level.hDeepGap level.hTI level.hWremJ level.hI level.hIsize level.hJsize level.hNI
    level.hJlow level.hJI level.hTcut level.hWcut level.hTdeep level.hWdeep level.f level.ρ
    level.hf level.D level.τweight level.hDlo level.hDhi level.weight level.hw level.Zinner
    level.hdtypesBase level.hsepBase level.hXimage level.hZimage level.hLocalSize level.hrows00 level.hconfigs00 level.hload00
    level.errR0 level.errI0 level.heR0 level.heI0 level.hErrR0 level.hErrI0 level.hZlow level.hrowEnd00
    level.hidxEnd00 level.errParent level.heP level.hNearP level.hMinP level.hTinner level.hErrParent level.hinnerSize
    level.hX level.hIotaSize level.hVhalf level.errInner level.errDeep level.heDeep level.hErrInner0 level.hErrDeep0
    level.hInnerBase level.hCutRBase level.hCutSBase level.hBalIBase level.hBalTBase

end Oberwolfach
