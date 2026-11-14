module

public import Oberwolfach.MarkedVortexParentInitialConfigurationFixed
public import Oberwolfach.MarkedVortexSeparateParentLocalTransfersParentDensity
public import Oberwolfach.MarkedVortexSeparatePotentialTransferParentDensity
public import Oberwolfach.MarkedVortexSeparateCommonTransferParentDensity
public import Oberwolfach.MarkedVortexSeparateDeepTransferParentDensity
public import Oberwolfach.MarkedVortexSeparateActiveEqTransferParentDensity
public import Oberwolfach.MarkedVortexSeparateActiveTransferParentDensity
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
theorem marked_vortex_corrected_complete_from_separate_parent_density_split
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
    (hcLocalEq:cLocal=Classical.choose (marked_vortex_initial_balance_from_parent_joint_local_changes r x hxPos etaBal hηBalPos))
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
  let hEq:∀i ≤ L,1  ≤  i  → 
      rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σold=
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σglobal ∧
      (fun b x u=>Hold b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u))=
        (fun b x u=>Hglobal b (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)) :=by
    have hrim:∀e:Sym2 V,e.toFinset⊆Q.extendedVertices 1 → σold (Sum.inl e)=σglobal (Sum.inl e):=by
      intro e he
      exact (hrawInner e he).symm
    have hspoke:∀b v u,v∈Q.extendedVertices 1 → u∈Q.extendedIndices 1 → (Hold b v u↔Hglobal b v u):=by
      intro b v u hv hu
      cases b with
      | false => simpa only [hHglobal,Bool.false_eq_true,ite_false] using hOrdinary v u hv hu
      | true => simp only [hHglobal,ite_true]
    have hh:=marked_vortex_protected_deeper_equality Q σold σglobal Hold Hglobal hrim hinterval hspoke
    intro i hi hi1
    exact hh i hi1
  let hOld:MarkedVortexCorrectedRecordConsequences r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κold thetaOld etaBal xold etaOld deltaI hIcut:=by
    rw [hraw,hspokes]
    exact marked_vortex_smaller_parent_to_record_consequences r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z hGood
      βA βrec κold hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq thetaOld hpot hdeep etaBal xold hxold hbal hmargin hterminal etaOld hrowmargin hloadmargin deltaI hIcut hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint
  let hCuts:((∀ mark,BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q 0)=>fun y:↥(markedVortexInnerVertices Q 0)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q 0)) (markedVortexPermutation Q π hpres 0) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut)) ∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q 0)=>fun u:↥(markedVortexInnerHubs Q 0)=>
      Hglobal mark
        (markedVortexVertexEmbedding Q 0 x.val) (markedVortexHubEmbedding Q 0 u.val))) deltaI (2*hIcut))) :=by
    rw [hHglobal]
    exact marked_vortex_initial_inner_cuts_from_raw_agreement V U Γ Color r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold
      βA βrec κold thetaOld etaBal xold etaOld deltaI hIcut hOld Hordinary hrawInner hOrdinary
  let hLocalAgreement:=marked_vortex_initial_local_agreement G D m β ε Q π hpres d σold σglobal Hold Hglobal hrawInner
    (by
      intro b v u hv hu
      cases b with
      | false => simpa only [hHglobal,Bool.false_eq_true,ite_false] using hOrdinary v u hv hu
      | true => simp only [hHglobal,ite_true])
  let hLocalSpokeBounds:=marked_vortex_initial_local_spoke_loss G D m β ε Q Hold Hglobal cLocal hPhysicalNoNew hPhysicalLoss
  let hJointTransfers:=marked_vortex_separate_parent_local_transfers_parent_density
    r k₀ d α ρ₀ sstar tstar kstar εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal htypes hsep βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld N NI Kgeom hα hαle hκle hxle hθle hηle hρ hs₀ hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo z hraw hspokes hGood hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hxold hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint iota ζchange ζactiveChange hηBalPos hxPos hiota hζchange hζactiveChange hepsBal hζBal hBalRelative hBalAmbient FR FS hinterval hR hS hFR hFS hsize hn hu pstar hpstar hplo hklo hslo hp1 hk1 hs1 hDlo hDhi Hordinary hHglobal hrawInner hOrdinary hboundaryHalf hκPos ωParent hωPos plo klo hploPos hkloPos hαeq hκoldEq hUlower hpLower hkLower ζFixed hζFixed hCfg hθDeepPos hθoldHalf hcycleDeep hpathDeep hηPos htstarPos FSactive hSactive hFSactive hnactive hβrect htt hactiveErr hactiveRow hDactiveLo hDactiveHi hρ₀Pos hρlo hρhi htstarCap hkstarPos hkstarCap hs₀Eq hζactiveCap cLocal hcLocalEq hLocalRimOutside hLocalSpokeOutside hPhysicalNoNew hPhysicalLoss hζFinal
  let hBalance:(let W:=markedVortexVertexType Q 0
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
      ∃ errInner errDeep:ℝ, 0 ≤ errDeep ∧
      errInner ≤ (x/2)*Fintype.card W ∧ errDeep ≤ (x/2)*Fintype.card W ∧
      (∀ v j,|bal I J v j| ≤ errInner) ∧
      (∀ v j,|bal T R v j| ≤ errDeep) ∧
      (∀ v j,|bal I J v j| ≤ etaBal*I.card)) :=hJointTransfers.1
  let hPotential:(let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let P:=G.comap (markedVortexVertexEmbedding Q 0)
      let ρ:=markedVortexPermutation Q π hpres 0
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q 0) (markedVortexHubEmbedding Q 0) σglobal
      let H:=fun b x u=>Hglobal b
        (markedVortexVertexEmbedding Q 0 x) (markedVortexHubEmbedding Q 0 u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q 0 u)
      let si:=fun u=>s (markedVortexHubEmbedding Q 0 u);
(let seed:=fun X:MarkedWheel (Prod.fst:W×W → W) Prod.snd Prod.fst Prod.snd (r+4) ρ (3*d)
          (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weightParent 0 X.1.val/(Dload*p^(r+4)*kval*s₀^(r+4));
        ∀ root:((W×W)⊕(W×W))⊕(Bool×W×Z),
          rawMarkedWheelMarginal P ρ d p kval qi si a j root≠0 → 
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d σ) H root-1| ≤ κ/4)) :=marked_vortex_separate_potential_transfer_parent_density
    r k₀ d α ρ₀ sstar tstar kstar εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal htypes hsep βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld N NI Kgeom hα hαle hκle hxle hθle hηle hρ hs₀ hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo z hraw hspokes hGood hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hxold hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint iota ζchange ζactiveChange hηBalPos hxPos hiota hζchange hζactiveChange hepsBal hζBal hBalRelative hBalAmbient FR FS hinterval hR hS hFR hFS hsize hn hu pstar hpstar hplo hklo hslo hp1 hk1 hs1 hDlo hDhi Hordinary hHglobal hrawInner hOrdinary hboundaryHalf hκPos ωParent hωPos plo klo hploPos hkloPos hαeq hκoldEq hUlower hpLower hkLower ζFixed hζFixed hCfg hθDeepPos hθoldHalf hcycleDeep hpathDeep hηPos htstarPos FSactive hSactive hFSactive hnactive hβrect htt hactiveErr hactiveRow hDactiveLo hDactiveHi hρ₀Pos hρlo hρhi htstarCap hkstarPos hkstarCap hs₀Eq hζactiveCap cLocal hcLocalEq hLocalRimOutside hLocalSpokeOutside hPhysicalNoNew hPhysicalLoss hζFinal
  let hBoundary:(let W:=markedVortexVertexType Q 0
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
      ∃ errR errI:ℝ,0 ≤ errR ∧ 0 ≤ errI ∧ errR ≤ (x/2)*Fintype.card W ∧ errI ≤ (x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (G.comap fP) ρ d (r+12) (X.image fA) p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
        MarkedIndicesWithSpokes ρ d (r+12) (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H) :=hJointTransfers.2
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
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0) ≤ (κ/4)*Fintype.card W) :=marked_vortex_separate_common_transfer_parent_density
    r k₀ d α ρ₀ sstar tstar kstar εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal htypes hsep βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld N NI Kgeom hα hαle hκle hxle hθle hηle hρ hs₀ hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo z hraw hspokes hGood hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hxold hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint iota ζchange ζactiveChange hηBalPos hxPos hiota hζchange hζactiveChange hepsBal hζBal hBalRelative hBalAmbient FR FS hinterval hR hS hFR hFS hsize hn hu pstar hpstar hplo hklo hslo hp1 hk1 hs1 hDlo hDhi Hordinary hHglobal hrawInner hOrdinary hboundaryHalf hκPos ωParent hωPos plo klo hploPos hkloPos hαeq hκoldEq hUlower hpLower hkLower ζFixed hζFixed hCfg hθDeepPos hθoldHalf hcycleDeep hpathDeep hηPos htstarPos FSactive hSactive hFSactive hnactive hβrect htt hactiveErr hactiveRow hDactiveLo hDactiveHi hρ₀Pos hρlo hρhi htstarCap hkstarPos hkstarCap hs₀Eq hζactiveCap cLocal hcLocalEq hLocalRimOutside hLocalSpokeOutside hPhysicalNoNew hPhysicalLoss hζFinal
  let hDeepRaw:let W:=markedVortexVertexType Q 0
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
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ
      (3*min βA (t/4)) (3*min βA (t/4)) σ H ∧
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) Dload p kval s₀ (weightParent 0) (thetaDeep/4) σ H :=marked_vortex_separate_deep_transfer_parent_density
    r k₀ d α ρ₀ sstar tstar kstar εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal htypes hsep βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld N NI Kgeom hα hαle hκle hxle hθle hηle hρ hs₀ hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo z hraw hspokes hGood hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hxold hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint iota ζchange ζactiveChange hηBalPos hxPos hiota hζchange hζactiveChange hepsBal hζBal hBalRelative hBalAmbient FR FS hinterval hR hS hFR hFS hsize hn hu pstar hpstar hplo hklo hslo hp1 hk1 hs1 hDlo hDhi Hordinary hHglobal hrawInner hOrdinary hboundaryHalf hκPos ωParent hωPos plo klo hploPos hkloPos hαeq hκoldEq hUlower hpLower hkLower ζFixed hζFixed hCfg hθDeepPos hθoldHalf hcycleDeep hpathDeep hηPos htstarPos FSactive hSactive hFSactive hnactive hβrect htt hactiveErr hactiveRow hDactiveLo hDactiveHi hρ₀Pos hρlo hρhi htstarCap hkstarPos hkstarCap hs₀Eq hζactiveCap cLocal hcLocalEq hLocalRimOutside hLocalSpokeOutside hPhysicalNoNew hPhysicalLoss hζFinal
  let hActiveEq:let f:=markedVortexActiveVertexEmbedding Q 1
      let g:=markedVortexNonDeeperHubToPhysical Q 0
      let ρ:=markedVortexActivePermutation Q π hpres 1;
      rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g σglobal)=
      rawMarkedPairRims (G.comap f) ρ d (rawMarkedRestrictPair f g z.1) :=marked_vortex_separate_activeeq_transfer_parent_density
    r k₀ d α ρ₀ sstar tstar kstar εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal htypes hsep βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld N NI Kgeom hα hαle hκle hxle hθle hηle hρ hs₀ hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo z hraw hspokes hGood hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hxold hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint iota ζchange ζactiveChange hηBalPos hxPos hiota hζchange hζactiveChange hepsBal hζBal hBalRelative hBalAmbient FR FS hinterval hR hS hFR hFS hsize hn hu pstar hpstar hplo hklo hslo hp1 hk1 hs1 hDlo hDhi Hordinary hHglobal hrawInner hOrdinary hboundaryHalf hκPos ωParent hωPos plo klo hploPos hkloPos hαeq hκoldEq hUlower hpLower hkLower ζFixed hζFixed hCfg hθDeepPos hθoldHalf hcycleDeep hpathDeep hηPos htstarPos FSactive hSactive hFSactive hnactive hβrect htt hactiveErr hactiveRow hDactiveLo hDactiveHi hρ₀Pos hρlo hρhi htstarCap hkstarPos hkstarCap hs₀Eq hζactiveCap cLocal hcLocalEq hLocalRimOutside hLocalSpokeOutside hPhysicalNoNew hPhysicalLoss hζFinal
  let hActiveRaw:let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let ρ:=markedVortexActivePermutation Q π hpres 1
    let t:=s₀/((r+4:ℕ):ℝ)
    let Dactive:=2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U D
    let fP:=markedVortexVertexEmbedding Q 0
    let gP:=markedVortexHubEmbedding Q 0
    let fA:=markedVortexNonDeeperVertexEmbedding Q 0
    let fnext:=markedVortexNextActiveInNonDeeper Q 0
    let gA:=markedVortexNonDeeperHubToParent Q 0
    let τP:=rawMarkedRestrictPair fP gP σglobal
    let HP:=fun b x u=>Hglobal b (fP x) (gP u);
    MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d Finset.univ
      (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d 1 Finset.univ p kval (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
      ((t/8)*Fintype.card W) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d (r+4) Dactive p kval s₀ (weight 1) (eta/4)
      (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) :=marked_vortex_separate_active_transfer_parent_density
    r k₀ d α ρ₀ sstar tstar kstar εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal htypes hsep βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld N NI Kgeom hα hαle hκle hxle hθle hηle hρ hs₀ hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo z hraw hspokes hGood hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hxold hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint iota ζchange ζactiveChange hηBalPos hxPos hiota hζchange hζactiveChange hepsBal hζBal hBalRelative hBalAmbient FR FS hinterval hR hS hFR hFS hsize hn hu pstar hpstar hplo hklo hslo hp1 hk1 hs1 hDlo hDhi Hordinary hHglobal hrawInner hOrdinary hboundaryHalf hκPos ωParent hωPos plo klo hploPos hkloPos hαeq hκoldEq hUlower hpLower hkLower ζFixed hζFixed hCfg hθDeepPos hθoldHalf hcycleDeep hpathDeep hηPos htstarPos FSactive hSactive hFSactive hnactive hβrect htt hactiveErr hactiveRow hDactiveLo hDactiveHi hρ₀Pos hρlo hρhi htstarCap hkstarPos hkstarCap hs₀Eq hζactiveCap cLocal hcLocalEq hLocalRimOutside hLocalSpokeOutside hPhysicalNoNew hPhysicalLoss hζFinal
  let hDeep:=marked_vortex_initial_deep_fields_for_record r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal
    βA βrec κ thetaDeep etaBal x eta deltaI hIcut hDeepRaw
  let hActive:=marked_vortex_initial_active_fields_for_record r (r+12) k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal
    βA βrec κ thetaDeep etaBal x eta deltaI hIcut hActiveRaw
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
  ∀ gammaLoss sigmaLoss:ℝ,
    (∀rho omega t:ℝ,ρ₀ ≤ rho → rho ≤ 1 → ρ₀/8 ≤ omega → omega ≤ 1 → tstar ≤ t → (r+4:ℝ)*t ≤ 1 → 
      ρ₀/400 ≤ rho*(r+4:ℝ)*t/2 → kstar ≤ rho*(r+4:ℝ)*t/2 → kstar ≤ rho*t/2 → kstar ≤ t → 
      ∀(Gamma Shade:Type) [Fintype Gamma] [Fintype Shade],
      ∀level:MarkedReferenceLevelData Gamma Shade r d N NI Kgeom (α/16) rho omega t kstar βA
        (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
        κ ξ thetaDeep (α/8) ω (ε/4) βrec (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
        eta x (ρ₀/16) hIcut deltaI etaBal,
      MarkedReferenceLevelStepProperty level gammaLoss sigmaLoss) → 
    ∀ sizeAbs aAbs bAbs eAbs fAbs:ℕ,∀ εabs:ℝ,
    let E:=MarkedSampleArc G π (3*d) (fun e=>σglobal (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>σglobal (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>Hglobal false z.1 z.2∨Hglobal true z.1 z.2);
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hglobal true) Finset.univ S (r+4) → 
    MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hglobal false) (Hglobal true) π (3*d) r sizeAbs aAbs bAbs eAbs fAbs εabs → 
    G.IsRegularOfDegree D → 0<D → ε≤εabs → 2*m≤sizeAbs →
    ∀(hγ:0<gammaLoss) (hσ:0<sigmaLoss),
    let NB:=Classical.choose (marked_vortex_terminal_budget eAbs gammaLoss sigmaLoss hγ hσ);
    NB≤Fintype.card V →
    HasResourceDecomposition (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (Hglobal false) (Hglobal true)=>markedWheelPhysicalResources W)
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π) (Hglobal false) (Hglobal true)) :=by
  intro hCapSpec hζCommonCap hζDeepCap hζActiveCap hζcap hζBoundaryCap hpotentialBudget hEq hOld hCuts hLocalAgreement hLocalSpokeBounds hJointTransfers hBalance hPotential hBoundary hRawCommon hDeepRaw hActiveEq hActiveRaw hDeep hActive hCommon hZero hOldBoundary hOldSpoke hWeights hRec hc R gammaLoss sigmaLoss hSteps
    sizeAbs aAbs bAbs eAbs fAbs εabs E K S hdiv habs hreg hD hεabs hterminalsize hγ hσ NB hNbudget
  obtain ⟨hsize,hV,hU⟩:=marked_vortex_terminal_decomposition_geometry G D m β ε εabs Q L sizeAbs fAbs
    hterminal hreg hn hD hρhi he hεabs hterminalsize
  obtain ⟨hgamma,hsigma⟩:=Classical.choose_spec (marked_vortex_terminal_budget eAbs gammaLoss sigmaLoss hγ hσ)
    V U G D m β ε Q hNbudget
  letI : ∀i,Fintype (R i).VP:=fun i=>(R i).inst7
  have hcard:Fintype.card (R ⟨0,by omega⟩).VP=Fintype.card (markedVortexVertexType Q 0):=rfl
  have hg:(eAbs:ℝ)≤gammaLoss*Fintype.card (R ⟨0,by omega⟩).VP:=by simpa only [hcard] using hgamma
  have hs:(eAbs:ℝ)≤sigmaLoss*Fintype.card (R ⟨0,by omega⟩).VP:=by simpa only [hcard] using hsigma
  have hsteps:∀i:Fin (L+1),MarkedReferenceLevelStepProperty (R i) gammaLoss sigmaLoss:=by
    obtain ⟨hρ₀1,hω,hω1,ht0,ht1,hp0,hp01,hk0,hk1,htle,hmt,hpBound,hkBound,hkHalf,hkt⟩:=
      long_actual_reference_level_densities (r+4) (by omega) ρ₀ (initialIndexDensity U D) tstar kstar
        hρ₀Pos hρlo hρhi htstarPos htstarCap hkstarPos hkstarCap
    intro i
    have hh:=hSteps (initialIndexDensity U D) (ρ₀/8) (s₀/(((r+4):ℕ):ℝ)) hρlo hρhi le_rfl hω1
      (by simpa only [hs₀Eq] using htle)
      (by simpa only [hs₀Eq,Nat.cast_add,Nat.cast_ofNat] using hmt)
      (by simpa only [hs₀Eq,Nat.cast_add,Nat.cast_ofNat] using hpBound)
      (by simpa only [hs₀Eq,Nat.cast_add,Nat.cast_ofNat] using hkBound)
      (by simpa only [hs₀Eq] using hkHalf) (by simpa only [hs₀Eq] using hkt) Γ Color
    exact hh (R i)
  have hh:=marked_vortex_corrected_complete_from_reserved r k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σglobal Hglobal htypes hsep
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hWeights.1 hWeights.2 hGeo hRec
    gammaLoss sigmaLoss hsteps sizeAbs aAbs bAbs eAbs fAbs εabs hdiv habs hsize hV hU
  apply hh
  · convert hg using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  · convert hs using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
