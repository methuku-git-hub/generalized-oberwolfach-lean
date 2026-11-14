module

public import Oberwolfach.MarkedMatchingSampleWeightedSelector
public import Oberwolfach.MarkedCommonNamedActualDensityDecomposition
public import Oberwolfach.LongActualUniformReferenceLevelStep
public import Oberwolfach.MarkedCommonNamedUniformSurvivingMixedDecomposition
public import Oberwolfach.LongActualSurvivingMixedRemainderDecomposition
public import Oberwolfach.LongActualMixedRemainderDecomposition
public import Oberwolfach.MarkedActualSampleRemainingMatchingDisjoint
public import Oberwolfach.MarkedCommonNamedSmallerReferenceTerminalChain
public import Oberwolfach.MarkedVortexConcreteCorrectedIteration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 100000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance directSampleMatchingDensityFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n:ℕ} {U:Type} [Fintype U] [Nonempty (Fin n)] [DecidableEq U]
local notation "V" => Fin n
theorem marked_direct_sample_matching_actual_density_decomposition
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Bool→ℝ) (s:U→Bool→ℝ)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut:ℝ) (N NI Kgeom:ℕ)
    (hd:1≤d) (he:0≤ε)
    (hp:p=initialIndexDensity U D*s₀/2) (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u false=s₀/(((r+4):ℕ):ℝ)) (hs0:∀u,s u false=s₀)
    (hXi0:0≤xiDeep) (hXiScale:(4*Kgeom+3*r+50:ℝ)*xiDeep≤κ/2)
    (hDeepGap:(1+2/initialIndexDensity U D)*xiDeep≤(s₀/(((r+4):ℕ):ℝ))*ω/32)


    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hIcut ξ xiDeep ω x N NI L)
    (hβA:βA≤βCommon) (hζκ:ζCommon≤κ/4)
    (hC:3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
    (hP:3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
    (hrec:βrec≤βA) (herr:tolRef+(r+12:ℕ)*ζActive≤κ/4) (hζActiveK:ζActive≤κ/4)
    (hεeq:εref≤κ/4) (hδeq:δref=κ)
    (hpot:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent≤κ/4)
    (hdeep:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent≤thetaDeep/4)
    (hx:0≤x) (hbal:epsBal+((r+4)+2:ℕ)*ζBal≤etaBal)
    (hmargin:epsBal+((r+4)+2:ℕ)*ζBal≤x/2) (hterminal:L+1=Q.length)
    (hrowmargin:rowErr+ζRow≤(s₀/((r+4:ℕ):ℝ))/8)
    (hloadmargin:τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*ζWide≤eta/4)
    (hbquarter:β≤1/4) (hh:0≤hIcut) (hδα:deltaI≤(α/2)/32) (hδstar:deltaI≤kstar/32)
    (hδt:2*deltaI≤tstar/8) (hhstar:2*hIcut≤(α/2)*kstar/4) (hhs:2*hIcut≤tstar/8-ζCut)
    (hEndpoint:tolRef+(r+12:ℕ)*ζActive≤x/2)
    (sizeCorr aCorr bCorr eCorr fCorr:ℕ) (gammaLoss sigmaLoss ξCorr εCorr ζCorr:ℝ) (hξCorr:0≤ξCorr)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*Fintype.card V)≤
      min (gammaLoss*Fintype.card V) (sigmaLoss*Fintype.card V))
    (hreg:G.IsRegularOfDegree D) (hD:0<D) (hρhi:initialIndexDensity U D≤1)
    (heCorr:ε≤εCorr) (hsizeCorr:2*m≤sizeCorr)
    (extra:ℝ)
    (mass:MarkedExpandedActualOutcome (U:=U) π d→ℝ)
    (levelOK:(∀i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)→Prop)
    (Prior Tail:(∀i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)→
      MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (Common:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (sample:MarkedExpandedActualOutcome (U:=U) π d)

    (hMatching:∃ (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ),
      ∃ hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i),
      ∃ hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i),
      ∃ levelWeight,levelOK levelWeight ∧
      0<mass sample ∧ Prior levelWeight sample ∧
      (MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d sample)) ∧ Common sample ∧ (MarkedProtectedAbsorbableCorrectionWithBounds G π d r sizeCorr aCorr bCorr eCorr fCorr εCorr ζCorr ξCorr (markedExpandedActualSelected π d sample).1
      (retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d sample).1 (Sum.inr e)) false (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d sample).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d sample).2 false false)
      (Q.extendedVertices 1) (Q.extendedIndices 1)) ∧ Tail levelWeight sample)
    (hρ₀pos:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D)
    (htstarpos:0<tstar) (htstarcap:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (hkstarpos:0<kstar) (hkstarcap:kstar≤ initialIndexDensity U D*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hs₀:s₀=(1/100:ℝ))
    (hSteps:∀rho omega t:ℝ,ρ₀≤rho → rho≤1 → ρ₀/8≤omega → omega≤1 → tstar≤t → (r+4:ℝ)*t≤1 →
      ρ₀/400≤rho*(r+4:ℝ)*t/2 → kstar≤rho*(r+4:ℝ)*t/2 → kstar≤rho*t/2 → kstar≤t →
      ∀(Gamma Color:Type) [Fintype Gamma] [Fintype Color],
      ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom (α/16) rho omega t kstar βA
        (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
        κ ξ thetaDeep (α/8) ω (ε/4) βrec (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
        eta x (ρ₀/16) hIcut deltaI etaBal,
        MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra)):
    ∃ (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ),
    ∃ hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i),
    ∃ hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i),
    ∃ outcome,0<mass outcome ∧ (((∃ levelWeight,levelOK levelWeight ∧ Prior levelWeight outcome ∧ Tail levelWeight outcome) ∧ (Common outcome ∧ outcome=sample)) ∧ (MarkedProtectedAbsorbableCorrectionWithBounds G π d r sizeCorr aCorr bCorr eCorr fCorr εCorr ζCorr ξCorr (markedExpandedActualSelected π d outcome).1
      (retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d outcome).2 false false)
      (Q.extendedVertices 1) (Q.extendedIndices 1))) ∧ ∃ hGood:MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome),
  let hRec:=marked_vortex_parent_smaller_reference_event_consequences r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome) hGood βA βrec κ thetaDeep etaBal x eta deltaI hIcut
    hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hx hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint

  (let hc:0<L+1:=by omega
  let R:=fun i:Fin (L+1)=>marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome)
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec i.val (by omega)
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  Nonempty (MarkedFiniteReferenceChain hc R)) ∧
  (let H:=retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d outcome).2 false false
  let E:=MarkedSampleArc G π (3*d) (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inl e)) false
  let K:=MarkedSampleArc G π (3*d) (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inl e)) true
  let R:=marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome)
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec 0 (by omega)
  letI : Fintype R.VP:=R.inst7
  letI : Fintype R.UP:=R.inst8
  letI : LinearOrder R.VP:=R.inst9
  letI : DecidableEq R.UP:=R.inst10
∃ (DA:Finset (E⊕K)) (DS:Finset (V×U)) (D₀:MarkedReferenceDeletion G π d (markedExpandedActualSelected π d outcome).1),
    D₀.arcs=DA ∧ D₀.spokes=DS ∧
    D₀.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1) (gammaLoss*Fintype.card V) (sigmaLoss*Fintype.card V) ∧
    MarkedDeletionAvoidsApproximateMatching G π d outcome D₀ ∧
    (let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (outcome.1 e)
    let Rmatch:Type:={x // x∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims G π d raw)
      (rawMarkedPairSpokes π d raw true true))}
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀ (Cmatch:Type) [Fintype Cmatch] [DecidableEq Cmatch] (Qc:Cmatch→Finset Rmatch) (M:Finset Cmatch),
      Disjoint ((M.biUnion Qc).image (fun w=>physicalResourceToFinite (φ w))) (D₀.remaining H)) ∧
  ∃ T:MarkedReferenceDeletion R.PP R.πP d R.σBase,
    T.Valid R.HBase (r+4) R.I R.J (gammaLoss*Fintype.card R.VP) (sigmaLoss*Fintype.card R.VP) ∧
    T.removed.image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=D₀.removed ∧
    (T.remaining R.HBase).image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=D₀.remaining H ∧
    let σ':=rawMarkedDeleteRims (markedExpandedActualSelected π d outcome).1 (markedSampleArcSetGraph G π d (markedExpandedActualSelected π d outcome).1 DA).edgeFinset
    let H':=markedDeletePhysicalSpokes H (markedFiniteSpokeGraph DS)
    let E':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc G π (3*d) (fun e=>σ' (Sum.inl e)) true;
    MarkedReservedTerminalAbsorberProperty (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r sizeCorr aCorr bCorr eCorr fCorr εCorr ∧
      (∀ F₀:Finset (Finset V⊕(V×U)), F₀.card≤fCorr → (eCorr:ℝ)≤extra*Fintype.card V →
  ∃ C:MarkedSupportedEdgeSet (fun x:E'=>x.val.1) (fun x=>x.val.2)
      (fun x:K'=>x.val.1) (fun x=>x.val.2) π U,
    Disjoint C.edges F₀ ∧ C.edges.card≤eCorr ∧ C.rows.card≤aCorr ∧ C.hubs.card≤bCorr ∧
    MarkedFixedTerminalAbsorber G π d (r+4) σ' H' C.edges (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
    MarkedFixedTerminalAbsorber G π d (r+4) (markedExpandedActualSelected π d outcome).1 H C.edges
      (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) ∧
  ∃ D₂:MarkedReferenceDeletion G π d (markedExpandedActualSelected π d outcome).1,
    D₂.Valid H (r+4) (Q.extendedVertices 1) (Q.extendedIndices 1)
      ((gammaLoss+extra)*Fintype.card V) ((sigmaLoss+extra)*Fintype.card V) ∧
    MarkedDeletionAvoidsApproximateMatching G π d outcome D₂ ∧
    D₂.removed=D₀.removed∪C.edges ∧ D₂.remaining H=D₀.remaining H\C.edges ∧ Disjoint D₀.removed C.edges ∧
  ∃ T:MarkedReferenceDeletion R.PP R.πP d R.σBase,
    T.Valid R.HBase (r+4) R.I R.J ((gammaLoss+extra)*Fintype.card R.VP) ((sigmaLoss+extra)*Fintype.card R.VP) ∧
    T.removed.image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=D₂.removed ∧
    (T.remaining R.HBase).image (markedResourceEmbedding (markedVortexVertexEmbedding Q 0).toEmbedding (markedVortexHubEmbedding Q 0))=D₂.remaining H ∧
    (let hc:0<L+1:=by omega
  let R:=fun i:Fin (L+1)=>marked_vortex_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome)
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo hRec i.val (by omega)
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  HasResourceDecomposition
        (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
          (r+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources W) (D₀.remaining H) ∧
      (∀ (Kmix:ℕ) (ℓ:Fin Kmix→ℕ) (Del:SimpleGraph V),
        let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (outcome.1 e)
        let state:=typedMarkedResourceState (rawMarkedPairRims G π d raw) (rawMarkedPairSpokes π d raw true true)
        let Tmix:=bernoulliVertexSet state
        let Smix:=longRawSurvivingResources G π d raw true true Del.edgeFinset
        let e:{v // v∈Tmix}↪_:=Function.Embedding.subtype _
        let eS:{v // v∈Smix}↪_:=Function.Embedding.subtype _
        let RmixSeed:=longRawSeedResources (U:=U) π d (r+4) ℓ
        let q:=survivingCandidateEmbedding (mixedCandidateResources RmixSeed) Smix Tmix
          (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
        let lift:=mixedRestrictedPhysicalLift RmixSeed e (longRawRealizeComponent G π d (r+4) raw true true ℓ)
        let B:=longRawRealizedPhysicalResources G π d (r+4) raw true true ℓ
        let Wref:=MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2) (fun e:K=>e.val.1) (fun e=>e.val.2)
          (r+4) π (3*d) (H false) (H true)
        let Wmix:=Σi,LongRawRealizedWheel G π d (r+4) raw true true ℓ i
        let Rref:Wref→Finset (Finset V⊕(V×U)):=fun w=>markedWheelPhysicalResources w
        let Rmix:Wmix→Finset (Finset V⊕(V×U)):=fun w=>B w.1 w.2;
        ∀M:Finset (RestrictedResource (mixedCandidateResources RmixSeed) eS),
        (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources RmixSeed) eS c)
          (restrictedResourceSet (mixedCandidateResources RmixSeed) eS c')) →
        HasResourceDecomposition (Sum.elim Rref Rmix) ((D₀.remaining H)∪(M.map q).biUnion (fun c=>Rmix (lift c))))))) := by
  have hMatching' : ∃ (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ),
      ∃ hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i),
      ∃ hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i),
      ∃ levelWeight,levelOK levelWeight ∧
      ∃ outcome,0<mass outcome ∧ Prior levelWeight outcome ∧
      (MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d outcome)) ∧ (Common outcome ∧ outcome=sample) ∧ (MarkedProtectedAbsorbableCorrectionWithBounds G π d r sizeCorr aCorr bCorr eCorr fCorr εCorr ζCorr ξCorr (markedExpandedActualSelected π d outcome).1
      (retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d outcome).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d outcome).2 false false)
      (Q.extendedVertices 1) (Q.extendedIndices 1)) ∧ Tail levelWeight outcome := by
    obtain ⟨weightParent,weight,hPW,hAW,levelWeight,hLevel,hMass,hPrior,hParent,hCommon,hCorr,hTail⟩:=hMatching
    exact ⟨weightParent,weight,hPW,hAW,levelWeight,hLevel,sample,hMass,hPrior,hParent,⟨hCommon,rfl⟩,hCorr,hTail⟩
  have hSample:=marked_matching_sample_supplies_weighted_selector r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s
    sizeCorr aCorr bCorr eCorr fCorr εCorr ζCorr ξCorr mass (fun w=>Common w ∧ w=sample) levelOK Prior Tail hMatching'
  exact marked_common_named_weighted_actual_density_decomposition r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap
    hGeo hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hx hbal hmargin hterminal
    hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint
    sizeCorr aCorr bCorr eCorr fCorr gammaLoss sigmaLoss ξCorr εCorr ζCorr hξCorr hbudget hreg hD hρhi heCorr hsizeCorr
    extra mass (fun outcome=>∃ levelWeight,levelOK levelWeight ∧ Prior levelWeight outcome ∧ Tail levelWeight outcome)
    (fun w=>Common w ∧ w=sample) hSample hρ₀pos hρlo htstarpos htstarcap hkstarpos hkstarcap hs₀ hSteps
end Oberwolfach
