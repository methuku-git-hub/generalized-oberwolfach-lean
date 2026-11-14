module

public import Oberwolfach.MarkedVortexInitialBalanceParentExplicitJointLocal
public import Oberwolfach.MarkedVortexInitialBalanceParentJointLocal
public import Oberwolfach.MarkedVortexInitialBoundaryParentFullyLocal
public import Oberwolfach.MarkedVortexInitialLocalSpokeLoss
public import Oberwolfach.MarkedVortexFixedMarginLocalCorrectionCap
public import Oberwolfach.MarkedVortexInitialBalanceParentAmbientLocal
public import Oberwolfach.MarkedVortexCorrectedCompleteExactDeeper
public import Oberwolfach.MarkedVortexTerminalBudget
public import Oberwolfach.MarkedVortexTerminalDecompositionGeometry
public import Oberwolfach.MarkedVortexCorrectedCompleteFromReserved
public import Oberwolfach.MarkedVortexSmallerParentToRecordConsequences
public import Oberwolfach.MarkedVortexInitialInnerCutsFromRawAgreement
public import Oberwolfach.MarkedVortexInitialBalanceFromSelectedParent
public import Oberwolfach.MarkedVortexInitialPotentialFromParentRecord
public import Oberwolfach.MarkedVortexInitialBoundaryFromParentRecord
public import Oberwolfach.MarkedVortexInitialCommonFromParentRecord
public import Oberwolfach.MarkedVortexInitialDeepFromParentRecord
public import Oberwolfach.MarkedVortexActiveTransferFixedMargin
public import Oberwolfach.MarkedVortexFirstActiveExactRims
public import Oberwolfach.MarkedVortexProtectedDeeperEquality
public import Oberwolfach.MarkedVortexFixedMarginCorrectionCap
public import Oberwolfach.LongActualReferenceLevelDensities
public import Oberwolfach.MarkedLocalPrerequisiteMonotone
public import Oberwolfach.MarkedVortexInitialDeepFieldsForRecord
public import Oberwolfach.MarkedVortexInitialActiveFieldsForRecord
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
theorem marked_vortex_separate_common_transfer_parent_density_explicit_cap
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U → Γ → ℝ) (s:U → Color → ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1) → markedVortexVertexType Q i) → ℝ)
    (weight:∀i,(Fin (r+4+1) → ↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i))) → ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool → V → U → Prop)
    (htypes:∀v u,¬(Hglobal false v u∧Hglobal true v u))
    (hsep:∀u v w,Hglobal false v u → Hglobal true w u → v≠π w)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld:ℝ) (N NI Kgeom:ℕ)
    (hα:0<α) (hαle:α ≤ αParent) (hκle:κold ≤ κ) (hxle:xold ≤ x) (hθle:thetaOld ≤ thetaDeep) (hηle:etaOld ≤ eta) (hρ:0  ≤  initialIndexDensity U D) (hs₀:0 ≤ s₀)
    (hd:1 ≤ d) (he:0 ≤ ε)
    (hp:p=initialIndexDensity U D*s₀/2) (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u a=s₀/(((r+4):ℕ):ℝ)) (hs0:∀u,s u j=s₀)
    (hXi0:0 ≤ xiDeep) (hXiScale:(4*Kgeom+3*r+50:ℝ)*xiDeep ≤ κ/2)
    (hDeepGap:(1+2/initialIndexDensity U D)*xiDeep ≤ (s₀/(((r+4):ℕ):ℝ))*ω/32)
    (hParentWeight:∀i ≤ L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (αParent/4)) (successorWeightUpper k₀ (αParent/4)) (weightParent i))
    (hActiveWeight:∀i ≤ L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (αParent/4)) (successorWeightUpper k₀ (αParent/4)) (weight i))
    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hIcut ξ xiDeep ω x N NI L)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hraw:σold=z.1)
    (hspokes:Hold=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j)
    (hGood:MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z)
    (hβA:βA ≤ βCommon) (hζκ:ζCommon ≤ κold/4)
    (hC:3*βA ≤ markedLocalCycleCoefficient r (αParent/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
    (hP:3*βA ≤ markedLocalPathCoefficient r (αParent/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
    (hrec:βrec ≤ βA) (herr:tolRef+(r+12:ℕ)*ζActive ≤ κold/4) (hζActiveK:ζActive ≤ κold/4)
    (hεeq:εref ≤ κold/4) (hδeq:δref=κold)
    (hpot:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent ≤ κold/4)
    (hdeep:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent ≤ thetaOld/4)
    (hxold:0 ≤ xold) (hbal:epsBal+((r+4)+2:ℕ)*ζBal ≤ etaBal)
    (hmargin:epsBal+((r+4)+2:ℕ)*ζBal ≤ xold/2) (hterminal:L+1=Q.length)
    (hrowmargin:rowErr+ζRow ≤ (s₀/((r+4:ℕ):ℝ))/8)
    (hloadmargin:τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*ζWide ≤ etaOld/4)
    (hbquarter:β ≤ 1/4) (hh:0 ≤ hIcut) (hδα:deltaI ≤ (αParent/2)/32) (hδstar:deltaI ≤ kstar/32)
    (hδt:2*deltaI ≤ tstar/8) (hhstar:2*hIcut ≤ (αParent/2)*kstar/4) (hhs:2*hIcut ≤ tstar/8-ζCut)
    (hEndpoint:tolRef+(r+12:ℕ)*ζActive ≤ xold/2)
    (iota ζchange ζactiveChange:ℝ) (hηBalPos:0<etaBal) (hxPos:0<x) (hiota:0 < iota)
    (hζchange:0 ≤ ζchange) (hζactiveChange:0 ≤ ζactiveChange)

    (hepsBal:0 ≤ epsBal) (hζBal:0 ≤ ζBal)
    (hBalRelative:epsBal+((r+4)+2:ℕ)*ζBal ≤ etaBal/2)
    (hBalAmbient:epsBal+((r+4)+2:ℕ)*ζBal ≤ x/4)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hinterval:∀e,σold (Sum.inr e)=σglobal (Sum.inr e))
    (hR:∀e,¬(rawMarkedPairRims G π d σold e↔rawMarkedPairRims G π d σglobal e) → markedPairPhysical π e∈FR.edgeFinset)
    (hS:∀b v u,¬(Hold b v u↔Hglobal b v u) → FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ) ≤ ζchange*Fintype.card V)
    (hFS:∀z,(FS.degree z:ℝ) ≤ ζchange*Fintype.card V)
    (hsize:iota*Fintype.card (markedVortexVertexType Q 0) ≤ ((markedVortexInnerVertices Q 0).card:ℝ))
    (hn:0<Fintype.card V) (hu:Fintype.card U ≤ Fintype.card V) (pstar:ℝ) (hpstar:0<pstar)
    (hplo:pstar ≤ p) (hklo:pstar ≤ kval) (hslo:pstar ≤ s₀) (hp1:p ≤ 1) (hk1:kval ≤ 1) (hs1:s₀ ≤ 1)
    (hDlo:(Fintype.card (markedVortexVertexType Q 0):ℝ)/2 ≤ 2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D)
    (hDhi:2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D ≤ 2*Fintype.card (markedVortexVertexType Q 0))

    (Hordinary:V → U → Prop)
    (hHglobal:Hglobal=(fun b v u=>if b then Hold true v u else Hordinary v u))
    (hrawInner:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1 → σglobal (Sum.inl e)=σold (Sum.inl e))
    (hOrdinary:∀v u,v∈Q.extendedVertices 1 → u∈Q.extendedIndices 1 → (Hold false v u↔Hordinary v u))
    (hboundaryHalf:xold ≤ x/2)

    (hκPos:0<κ) (ωParent:ℝ) (hωPos:0<ωParent) (plo klo:ℝ) (hploPos:0<plo) (hkloPos:0<klo)
    (hαeq:αParent=2*α) (hκoldEq:κold=κ/2)
    (hUlower:ωParent*Fintype.card V ≤ (Fintype.card U:ℝ)) (hpLower:plo ≤ p) (hkLower:klo ≤ kval)

    (ζFixed:ℝ) (hζFixed:0<ζFixed) (hCfg:2*ζCfg ≤ ζFixed) (hθDeepPos:0<thetaDeep) (hθoldHalf:thetaOld ≤ thetaDeep/2)
    (hcycleDeep:3*βA ≤ markedLocalCycleCoefficient r (αParent/2) (tstar/2) kstar-(r+5:ℕ)*ζFixed)
    (hpathDeep:3*βA ≤ markedLocalPathCoefficient r (αParent/2) (tstar/2) kstar-(r+4:ℕ)*ζFixed)

    (hηPos:0<eta) (htstarPos:0<tstar)

    (FSactive:SimpleGraph (↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))⊕markedVortexNonDeeperHubType Q 0))
    (hSactive:let f:=markedVortexActiveVertexEmbedding Q 1
      let g:=markedVortexNonDeeperHubToPhysical Q 0
      let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
      ∀b v u,¬(H b (f v) (g u)↔Hglobal b (f v) (g u)) → FSactive.Adj (Sum.inl v) (Sum.inr u))
    (hFSactive:∀u,(FSactive.degree (Sum.inr u):ℝ) ≤ ζactiveChange*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)))
    (hnactive:0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)))
    (hβrect:βrec ≤ (s₀/((r+4:ℕ):ℝ))/4) (htt:tstar ≤ s₀/((r+4:ℕ):ℝ))
    (hactiveErr:τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*ζWide ≤ eta/8)
    (hactiveRow:rowErr+ζRow ≤ tstar/16)
    (hDactiveLo:(Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)):ℝ)/2 ≤ 
      2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U D)
    (hDactiveHi:2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U D ≤ 
      2*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)))
    (hρ₀Pos:0<ρ₀) (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D ≤ 1)
    (htstarCap:tstar ≤ (1/100)/(((r+4):ℕ):ℝ)) (hkstarPos:0<kstar)
    (hkstarCap:kstar ≤ initialIndexDensity U D*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hs₀Eq:s₀=(1/100:ℝ))
    (hζactiveCap:ζactiveChange≤Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r αParent tstar kstar ζFixed eta
      (successorWeightUpper k₀ (αParent/4)) pstar hζFixed hηPos
      (successorWeightConstants_pos k₀ (αParent/4) (by have hh:=lt_of_lt_of_le hα hαle;positivity)).2.le hpstar htstarPos))
    (cLocal:ℝ)
    (hcLocalEq:cLocal=markedExplicitJointLocalCap (r+4) (r+12) etaBal x)
    (hLocalRimOutside:∀v,v∉Q.extendedVertices 1→(FR.degree v:ℝ)≤cLocal*((markedVortexInnerVertices Q 0).card:ℝ))
    (hLocalSpokeOutside:∀B:Finset U,∀v,v∉Q.extendedVertices 1→
      (∑u∈B,if ¬(Hold false v u↔Hglobal false v u) then (1:ℝ) else 0)≤cLocal*((markedVortexInnerVertices Q 0).card:ℝ))
    (hPhysicalNoNew:∀u v,v∈Q.extendedVertices 1→Hglobal false v u→Hold false v u)
    (hPhysicalLoss:∀u,(((Q.extendedVertices 1).filter (fun v=>Hold false v u ∧ ¬Hglobal false v u)).card:ℝ)≤
      cLocal*((markedVortexInnerVertices Q 0).card:ℝ))
    (hζFinal:ζchange ≤ Classical.choose (marked_vortex_fixed_margin_local_correction_cap r κ αParent ωParent plo klo tstar kstar ζFixed thetaDeep (1:ℝ)
      (successorWeightUpper k₀ (αParent/4)) pstar (1:ℝ) (1:ℝ) (1:ℝ)
      hκPos (lt_of_lt_of_le hα hαle) hωPos hploPos hkloPos htstarPos hζFixed hθDeepPos (by norm_num)
      (successorWeightConstants_pos k₀ (αParent/4) (by have hh:=lt_of_lt_of_le hα hαle;positivity)).2.le
      hpstar (by norm_num) (by norm_num) (by norm_num)))
:
  let W:=markedVortexVertexType Q 0
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
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0) ≤ (κ/4)*Fintype.card Z) ∧
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0) ≤ (κ/4)*Fintype.card W) :=by
  let hCapSpec:=Classical.choose_spec (marked_vortex_fixed_margin_local_correction_cap r κ αParent ωParent plo klo tstar kstar ζFixed thetaDeep (1:ℝ)
      (successorWeightUpper k₀ (αParent/4)) pstar (1:ℝ) (1:ℝ) (1:ℝ)
      hκPos (lt_of_lt_of_le hα hαle) hωPos hploPos hkloPos htstarPos hζFixed hθDeepPos (by norm_num)
      (successorWeightConstants_pos k₀ (αParent/4) (by have hh:=lt_of_lt_of_le hα hαle;positivity)).2.le
      hpstar (by norm_num) (by norm_num) (by norm_num))
  let hζCommonCap:=hζFinal.trans hCapSpec.2.1
  let hζDeepCap:=hζFinal.trans hCapSpec.2.2.1
  let hζActiveCap:=hζFinal.trans hCapSpec.2.2.2.1
  let hζcap:=hζFinal.trans hCapSpec.2.2.2.2.1
  let hζBoundaryCap:=hζFinal.trans hCapSpec.2.2.2.2.2.1
  let hpotentialBudget:κold/4+33*((r+4:ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/pstar^(2*(r+4)+1))*ζchange ≤ κ/4:=by
    simpa only [hκoldEq] using hCapSpec.2.2.2.2.2.2 ζchange hζchange hζFinal
  let hOld:MarkedVortexCorrectedRecordConsequences r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κold thetaOld etaBal xold etaOld deltaI hIcut:=by
    rw [hraw,hspokes]
    exact marked_vortex_smaller_parent_to_record_consequences r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z hGood
      βA βrec κold hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq thetaOld hpot hdeep etaBal xold hxold hbal hmargin hterminal etaOld hrowmargin hloadmargin deltaI hIcut hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint
  let hRawCommon:let W:=markedVortexVertexType Q 0
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
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0) ≤ (κ/4)*Fintype.card Z) ∧
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0) ≤ (κ/4)*Fintype.card W) :=by
    have ht:=(Classical.choose_spec (marked_vortex_initial_common_from_parent_record r κ αParent ωParent plo klo
      hκPos (lt_of_lt_of_le hα hαle) hωPos hploPos hkloPos)).2
    have hOldHalf:MarkedVortexCorrectedRecordConsequences r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec (κ/2) thetaOld etaBal xold etaOld deltaI hIcut:=by
      simpa only [←hκoldEq] using hOld
    have hh:=ht ζchange hζchange hζCommonCap V U Γ Color (r+12) k₀ d ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal
      βA βrec thetaOld etaBal xold etaOld deltaI hIcut hp hk hOldHalf FR FS hn hUlower hinterval hR hS hFR hFS
      (by rw [hspokes];intro v u;exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) a _ z.2 a j v u) hpLower hkLower
    have ha:(2*α)/16=2*(α/16):=by ring
    simpa only [hαeq,ha] using hh
  exact hRawCommon
end Oberwolfach
