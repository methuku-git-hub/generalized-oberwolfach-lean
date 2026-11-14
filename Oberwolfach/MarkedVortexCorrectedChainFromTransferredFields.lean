module

public import Oberwolfach.MarkedVortexInitialCommonFieldsForRecord
public import Oberwolfach.MarkedVortexInitialRecordFieldsOfTransfers
public import Oberwolfach.MarkedVortexRecordConsequencesBoundaryToleranceMono
public import Oberwolfach.MarkedVortexRecordConsequencesSpokeToleranceMono
public import Oberwolfach.MarkedVortexCorrectedReferenceChain
public import Oberwolfach.MarkedVortexCorrectedRecordFromStrongerPreciseParent
public import Oberwolfach.MarkedVortexWeightFamiliesWeakenMargin
public import Oberwolfach.MarkedFiniteReferenceChain
public import Oberwolfach.MarkedVortexFiniteSampleChain

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
noncomputable def markedVortexCorrectedChainFromTransferredFields
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (htypes:∀v u,¬(Hglobal false v u∧Hglobal true v u))
    (hsep:∀u v w,Hglobal false v u→Hglobal true w u→v≠π w)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld:ℝ) (N NI Kgeom:ℕ)
    (hα:0<α) (hαle:α≤αParent) (hκle:κold≤κ) (hxle:xold≤x) (hθle:thetaOld≤thetaDeep) (hηle:etaOld≤eta) (hρ:0 ≤ initialIndexDensity U D) (hs₀:0≤s₀)
    (hd:1≤d) (he:0≤ε)
    (hp:p=initialIndexDensity U D*s₀/2) (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u a=s₀/(((r+4):ℕ):ℝ)) (hs0:∀u,s u j=s₀)
    (hXi0:0≤xiDeep) (hXiScale:(4*Kgeom+3*r+50:ℝ)*xiDeep≤κ/2)
    (hDeepGap:(1+2/initialIndexDensity U D)*xiDeep≤(s₀/(((r+4):ℕ):ℝ))*ω/32)
    (hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (αParent/4)) (successorWeightUpper k₀ (αParent/4)) (weightParent i))
    (hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (αParent/4)) (successorWeightUpper k₀ (αParent/4)) (weight i))
    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hIcut ξ xiDeep ω x N NI L)
    (hOld:MarkedVortexCorrectedRecordConsequences r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κold thetaOld etaBal xold etaOld deltaI hIcut)
    (hEq:∀i≤L,1 ≤ i →
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σold=
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σglobal ∧
      (fun b x u=>Hold b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u))=
        (fun b x u=>Hglobal b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)))
    (hRawCommon:     let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hpres 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let c:ℝ:=(r+4:ℕ)
    let t:=s₀/c
    let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D;
    MarkedReferenceStatistics P ρ d a j Dload (κ/4) κ (2*(α/16)) p kval (c*t) t σ ∧
    MarkedReferenceCutFamilies P ρ d a j (2*(α/16)) p kval t σ ∧
    MarkedCommonConfigurationsWithSpokes r P ρ d βA (κ/4) σ H ∧
    MarkedRowsWithSpokes P ρ d (r+12) Finset.univ p kval (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
    MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W))
    (hDeep: (let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:markedVortexNonDeeperHubType Q 0→markedVortexHubType Q 0:=Subtype.val
      let ρP:=markedVortexPermutation Q π hpres 0
      let ρ:=markedVortexActivePermutation Q π hpres (0+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
MarkedLocalConfigurationsWithSpokes r (G.comap fP) ρP d Finset.univ
        (3*(min βA ((s₀/((r+4:ℕ):ℝ))/4))) (3*(min βA ((s₀/((r+4:ℕ):ℝ))/4))) σP HP) ∧ (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let P:=G.comap (markedVortexVertexEmbedding Q 0)
      let ρ:=markedVortexPermutation Q π hpres 0
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal
      let H:=fun b x u=>Hglobal b
        (markedVortexVertexEmbedding Q 0 x) (markedVortexHubEmbedding Q 0 u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q 0 u)
      let si:=fun u=>s (markedVortexHubEmbedding Q 0 u);
MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) Dload p kval s₀ (weightParent 0) (thetaDeep/4) σ H))
    (hActive: (let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:markedVortexNonDeeperHubType Q 0→markedVortexHubType Q 0:=Subtype.val
      let ρP:=markedVortexPermutation Q π hpres 0
      let ρ:=markedVortexActivePermutation Q π hpres (0+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (f x))) ρ d Finset.univ
        (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
        (fun b x u=>HP b (fA (f x)) (gA u))) ∧ (let Z:=markedVortexHubType Q 0
      let Zkeep:=markedVortexNonDeeperHubType Q 0
      let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:Zkeep→Z:=Subtype.val
      let ρ:=markedVortexActivePermutation Q π hpres (0+1)
      let σP:=rawMarkedRestrictPair fP gP σglobal
      let HP:=fun b x u=>Hglobal b (fP x) (gP u);
      MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d 1 Finset.univ p kval
        (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
        (((s₀/((r+4:ℕ):ℝ))/8)*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (0+1)):Finset (markedVortexVertexType Q (0+1))))
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u)) ∧
      MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d (r+4) ((2*(((Finset.univ\markedVortexInnerHubs Q (0+1)):Finset (markedVortexHubType Q (0+1))).card:ℝ)/initialIndexDensity U D)) p kval s₀ (weight (0+1)) (eta/4)
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))))
    (hPotential: (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let P:=G.comap (markedVortexVertexEmbedding Q 0)
      let ρ:=markedVortexPermutation Q π hpres 0
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal
      let H:=fun b x u=>Hglobal b
        (markedVortexVertexEmbedding Q 0 x) (markedVortexHubEmbedding Q 0 u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q 0 u)
      let si:=fun u=>s (markedVortexHubEmbedding Q 0 u);
(let seed:=fun X:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd (r+4) ρ (3*d)
          (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weightParent 0 X.1.val/(Dload*p^(r+4)*kval*s₀^(r+4));
        ∀ root:((W×W)⊕(W×W))⊕(Bool×W×Z),
          rawMarkedWheelMarginal P ρ d p kval qi si a j root≠0→
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d σ) H root-1|≤κ/4)))
    (hBalance: (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let f:=markedVortexVertexEmbedding Q 0
      let g:=markedVortexHubEmbedding Q 0
      let ρ:=markedVortexPermutation Q π hpres 0
      let σ:=rawMarkedRestrictPair f g σglobal
      let H:=fun b x u=>Hglobal b (f x) (g u)
      let E:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) false
      let K:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) true
      let S:=Finset.univ.filter (fun s:W×Z=>H false s.1 s.2∨H true s.1 s.2)
      let I:=markedVortexInnerVertices Q 0
      let J:=markedVortexInnerHubs Q 0
      let T:=markedVortexDeeperVertices Q 0
      let R:=markedVortexDeeperHubs Q 0
      let bal:=markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S (r+4);
      ∃ errInner errDeep:ℝ, 0≤errDeep ∧
      errInner≤(x/2)*Fintype.card W ∧ errDeep≤(x/2)*Fintype.card W ∧
      (∀ v j,|bal I J v j|≤errInner) ∧
      (∀ v j,|bal T R v j|≤errDeep) ∧
      (∀ v j,|bal I J v j|≤etaBal*I.card)))
    (hCuts: ((∀ mark,BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q 0)=>fun y:↥(markedVortexInnerVertices Q 0)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q 0)) (markedVortexPermutation Q π hpres 0) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut)) ∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q 0)=>fun u:↥(markedVortexInnerHubs Q 0)=>
      Hglobal mark
        (markedVortexVertexEmbedding Q 0 x.val) (markedVortexHubEmbedding Q 0 u.val))) deltaI (2*hIcut))))
    (hBoundary: (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let ρ:=markedVortexPermutation Q π hpres 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:=markedVortexNonDeeperHubToParent Q 0
      let X:=Finset.univ.image f
      let Zinner:=markedVortexInnerNonDeeperHubs Q 0
      let ω:=rawMarkedRestrictPair fP gP σglobal
      let H:=fun b x u=>Hglobal b (fP x) (gP u);
      ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (G.comap fP) ρ d (r+12) (X.image fA) p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
        MarkedIndicesWithSpokes ρ d (r+12) (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H))
:
  let hCommon:=marked_vortex_initial_common_fields_for_record r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal
    βA βrec κ thetaDeep etaBal x eta deltaI hIcut hp hk hRawCommon
  let hZero:=marked_vortex_initial_record_fields_of_transfers r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal
    βA βrec κ thetaDeep etaBal x eta deltaI hIcut hCommon hDeep hActive hPotential hBalance hCuts hBoundary
  let hOldBoundary:=marked_vortex_record_consequences_boundary_tolerance_mono r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold
    βA βrec κold thetaOld etaBal xold etaOld deltaI hIcut x hxle hOld
  let hOldSpoke:=marked_vortex_record_consequences_spoke_tolerance_mono r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold
    βA βrec κold thetaOld etaBal x etaOld deltaI hIcut thetaDeep eta hθle hηle hOldBoundary
  let hWeights:=marked_vortex_weight_families_weaken_margin Q π hpres r k₀ d L αParent α τParent τ hα hαle weightParent weight hParentWeight hActiveWeight
  let hRec:=marked_vortex_corrected_record_from_stronger_precise_parent r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal
    βA βrec κ thetaDeep etaBal x eta deltaI hIcut α κold hαle hκle hρ hs₀ hOldSpoke hEq hZero
  let hc:0<L+1:=by omega
  let R:=fun i:Fin (L+1)=>marked_vortex_corrected_level_record_from_bundles_def r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal htypes hsep
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hWeights.1 hWeights.2 hGeo hRec i.val (by omega)
  letI : ∀ i,Fintype (R i).VP:=fun i=>(R i).inst7
  letI : ∀ i,Fintype (R i).UP:=fun i=>(R i).inst8
  letI : ∀ i,LinearOrder (R i).VP:=fun i=>(R i).inst9
  letI : ∀ i,DecidableEq (R i).UP:=fun i=>(R i).inst10
  MarkedFiniteReferenceChain hc R := by
  let hCommon:=marked_vortex_initial_common_fields_for_record r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal
    βA βrec κ thetaDeep etaBal x eta deltaI hIcut hp hk hRawCommon
  let hZero:=marked_vortex_initial_record_fields_of_transfers r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal
    βA βrec κ thetaDeep etaBal x eta deltaI hIcut hCommon hDeep hActive hPotential hBalance hCuts hBoundary
  let hOldBoundary:=marked_vortex_record_consequences_boundary_tolerance_mono r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold
    βA βrec κold thetaOld etaBal xold etaOld deltaI hIcut x hxle hOld
  let hOldSpoke:=marked_vortex_record_consequences_spoke_tolerance_mono r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold
    βA βrec κold thetaOld etaBal x etaOld deltaI hIcut thetaDeep eta hθle hηle hOldBoundary
  let hWeights:=marked_vortex_weight_families_weaken_margin Q π hpres r k₀ d L αParent α τParent τ hα hαle weightParent weight hParentWeight hActiveWeight
  let hRec:=marked_vortex_corrected_record_from_stronger_precise_parent r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal
    βA βrec κ thetaDeep etaBal x eta deltaI hIcut α κold hαle hκle hρ hs₀ hOldSpoke hEq hZero
  exact markedVortexCorrectedReferenceChain r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal htypes hsep
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hWeights.1 hWeights.2 hGeo hRec
end Oberwolfach
