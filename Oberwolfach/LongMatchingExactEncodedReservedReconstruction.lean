module

public import Oberwolfach.LongMatchingEncodedFactorReconstruction
public import Oberwolfach.LongMatchingExactEncodedReservedActualDensity
public import Oberwolfach.FirstVortexDensityIdentity
public import Oberwolfach.LongMatchingExactEncodedReservedActualChangeRates
public import Oberwolfach.FirstVortexConcreteStableCorrectionBounds
public import Oberwolfach.MarkedCommonRetainedSpokeBudget
public import Oberwolfach.LongMatchingCommonRetainedSpokeBounds
public import Oberwolfach.MarkedCommonSelectorGlobalBalanceBudget
public import Oberwolfach.LongMatchingCommonEvent
public import Oberwolfach.LongMatchingWitnessGraphsMinimalBalance
public import Oberwolfach.LongSameResidualEncodedChangeAndRobustTransfer
public import Oberwolfach.MarkedVortexProtectedDeeperEquality
public import Oberwolfach.LongMatchingWitnessChangeGraphsWithSpokeGeometry
public import Oberwolfach.LongCorrectedSampleDivisibleReserved
public import Oberwolfach.LongFactorComplementCorrectedSpokeGeometry
public import Oberwolfach.LongSameSampleVortexChangeGraphs
public import Oberwolfach.LongMatchingPhysicalCorrectionFields
public import Oberwolfach.LongSameSampleChangeGraphsFromReference
public import Oberwolfach.MarkedVortexActualResidualDeeperEquality

@[expose] public section
/-! The physical correction and its two change graphs retain the original
sample exactly on every positive vortex level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance exactEncodedReconstructFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance exactEncodedReconstructArc {n:ℕ} (P:Fin n×Fin n→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite
theorem long_matching_witness_exact_encoded_reserved_reconstruction
    {n Dclass:ℕ} [Nonempty (Fin n)]
    (F:Fin (Dclass/2)→SimpleGraph (Fin n)) (G S Del:SimpleGraph (Fin n))
    (hEven:Even Dclass) (hS:S.IsRegularOfDegree Dclass) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (z:MarkedExpandedActualOutcome (U:=Fin (Dclass/2)) π d) (M:Fin n→Fin n→ℕ) (I:Finset (Fin n)):
    let m:=r+4
    let ω:=z.1
    let raw:RawMarkedOutcome (Fin n) (Fin (Dclass/2)) Bool Bool:=fun e=>rawExpandedApproximateCollapse e (ω e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
    let J:=z.2;
    ∀ (Pack:Finset (Sym2 (Fin n))) (Enew:(Fin (Dclass/2))→Finset (Sym2 (Fin n))) (A:Finset (Fin n×Fin n))
    (R:(Fin (Dclass/2))→Finset (Fin n)) (θ δ ηphys ηdel ηtype lossRow lossCol ε ζ:ℝ)
    (hI:∀v,π v∈I↔v∈I)
    (hprov:LongFactorComplementProvenance F S G π d m raw t J Pack Enew A R)
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ)
    (Δ:ℝ) (K:ℕ) (Dmatch alpha γ eps βList:ℝ)
    (hF:∀u,(F u).IsRegularOfDegree 2) (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×(Fin (Dclass/2)))))
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del)
    (rhoCorr etaCorr ξClass:ℝ)
    (hηdelEq:ηdel=Δ*n)
    (hηphysEq:ηphys=(2*θ+2*max alpha (4*γ)+2*ξClass+5*Real.sqrt δ)*n+(n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ))
    (hηtypeEq:ηtype=(1+2/rhoCorr)*etaCorr*n+(n:ℝ)^(3/5:ℝ))
    (h:ℕ) (hh:1≤h)
    {DQ mm:ℕ} {β εQ:ℝ} (Q:Vortex (Fin (Dclass/2)) G DQ β εQ mm) (Hinner:Finset (Fin (Dclass/2)))
    (hIeq:I=Q.extendedVertices 1) (hHeq:Hinner=Q.extendedIndices 1),
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion Enew
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    let σ:RawMarkedOutcome (Fin n) (Fin (Dclass/2)) Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let ρ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d ρ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d ρ false t J false false
    let H₀:=fun v w=>v∈R w\Y w
    let HK:=retainedRawMarkedSpokes π d ρ false t J false true true
    let H':Bool→Fin n→(Fin (Dclass/2))→Prop:=fun b v w=>if b then HK v w else H₀ v w;
    Small.edgeFinset=A.image (fun a=>s(a.1,a.2))→
    ∀T:Finset {e:Fin n×Fin n // P e},
    ∀(τtarget:RawMarkedOutcome (Fin n) (Fin (Dclass/2)) Bool Bool),
    (∀e,τtarget (Sum.inr e)=σ (Sum.inr e)) →
    (∀e:Sym2 (Fin n),e.toFinset⊆I → τtarget (Sum.inl e)=σ (Sum.inl e)) →
    (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τtarget (Sum.inl e)) mark x y=1 ↔
      if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
      else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y) →
    (∀e∈T,longMarkedArcEligible π d e.val)→(∀e,e∉T→longOrdinaryArcEligible π d e.val)→
    (∀mark x y,x∈I→y∈I→
      (markedPhysicalRim G π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y))→
    MarkedRemainderDivisible (fun e:residualOrdinaryArc P T=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc P T=>e.val.val.1) (fun e=>π.symm e.val.val.2) HK Finset.univ
      (Finset.univ.filter (fun z:Fin n×(Fin (Dclass/2))=>H₀ z.1 z.2∨HK z.1 z.2)) m→
    ∀(hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (L sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon:ℕ)
      (ρ₀Host:ℝ) (hρ₀Host:0<ρ₀Host) (hDQ:0<DQ)
      (hρHostLo:ρ₀Host≤ initialIndexDensity (Fin (Dclass/2)) DQ) (hρHostHi:initialIndexDensity (Fin (Dclass/2)) DQ≤1)
      (hDQhi:(DQ:ℝ)≤2*n)
      (βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
        εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
        ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance:ℝ)
      (hγRich:0≤γRich)
      (levelWeight:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
      (hCommon:LongMatchingCommonEvent G π DQ mm β εQ Q hpres r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h
        F hF θ (initialIndexDensity (Fin (Dclass/2)) DQ) βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
        εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
        ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight (markedExpandedActualSelected π d z))
      (hBalanceScale:ε=ηBalance*n)
      (κaux κref ζret:ℝ) (hηBalance:0<ηBalance) (hκaux:0<κaux) (hκref:0≤κref) (hκrefCap:κref≤κaux)
      (hεRefEq:εRefEvent=κref/4) (hεNbr0:0≤εNbrEvent) (hεNbrCap:εNbrEvent≤κaux)
      (hκauxCap:κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1))),
    (∀v,((changed ((longSelectedPhysicalGraph G π d ω).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤
      (2*θ+2*max alpha (4*γ)+2*ξClass+5*Real.sqrt δ)*n+(n:ℝ)^(3/5:ℝ)+Δ*n+2*(6*d+2:ℕ))→
    (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤(1+2/rhoCorr)*etaCorr*n+(n:ℝ)^(3/5:ℝ))→
    κaux≤ζret→lossRow=ζret*n→lossCol=ζret*n→

    (∀w∈Hinner,∀v∈I,v∈R w\Y w↔H false v w)→
    ∀ (εStable ζStable capStable:ℝ) (sizeStable aStable bStable eStable fStable:ℕ),
    0≤ζStable→
    MarkedRetainedRobustChangeEvent G π d r false false εStable ζStable capStable sizeStable aStable bStable eStable fStable ⟨σ,J⟩→
    ∀cap:ℝ,0≤cap→cap≤capStable→ζ=min cap (1:ℝ)/2→
    ηphys+ηdel+ηtype≤cap*n→
    2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(ε+2*(ηphys+ηdel+ηtype))≤(min cap (1:ℝ)/2)*n→
    2*(lossRow+10*θ*n)+ε≤(min cap (1:ℝ)/2)*n→
    ∃(FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕(Fin (Dclass/2)))),
      (∀e,τtarget (Sum.inr e)=σ (Sum.inr e)) ∧
      (∀e:Sym2 (Fin n),e.toFinset⊆I→τtarget (Sum.inl e)=σ (Sum.inl e)) ∧
      (∀mark x y,markedPhysicalRim G π (3*d) (fun e=>τtarget (Sum.inl e)) mark x y=1 ↔
        if mark then ∃e:residualMarkedArc P T,e.val.val.1=x∧π.symm e.val.val.2=y
        else ∃e:residualOrdinaryArc P T,e.val.val.1=x∧e.val.val.2=y) ∧
      (∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τtarget a)→markedPairPhysical π a∈FR.edgeFinset) ∧
      (∀v,(FR.degree v:ℝ)≤ηphys+ηdel+ηtype) ∧
      (∀b v w,¬(H b v w↔H' b v w)→FS.Adj (Sum.inl v) (Sum.inr w)) ∧
      (∀z,(FS.degree z:ℝ)≤ζ*n) ∧
      (∀ (i:ℕ), 1 ≤ i →
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ=
        rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) τtarget ∧
        (fun b v u=>H b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))=
        (fun b v u=>H' b (markedVortexVertexEmbedding Q i v) (markedVortexHubEmbedding Q i u))) ∧
      (∀v u,¬(H' false v u∧H' true v u)) ∧
      (∀u v w,H' false v u→H' true w u→v≠π w) ∧
      let Sp:=Finset.univ.filter (fun p:Fin n×(Fin (Dclass/2))=>H' false p.1 p.2∨H' true p.1 p.2)
      let E:=MarkedSampleArc G π (3*d) (fun e=>τtarget (Sum.inl e)) false
      let K:=MarkedSampleArc G π (3*d) (fun e=>τtarget (Sum.inl e)) true;
      MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ Sp (r+4) ∧
      MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r sizeStable aStable bStable eStable fStable εStable ∧
      (HasResourceDecomposition (markedWheelPhysicalResources (tail:=fun e:E=>e.val.1) (head:=fun e:E=>e.val.2)
        (ktail:=fun e:K=>e.val.1) (khead:=fun e:K=>e.val.2) (m:=r+4) (π:=π) (b:=3*d) (H₀:=H' false) (Hₖ:=H' true))
        (markedDecompositionTarget (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e:E=>e.val.2)
          (fun e:K=>e.val.1) (fun e:K=>e.val.2) π) (H' false) (H' true)) → HasFactorDecomposition S F) :=by
  intro m ω raw t J Pack Enew A R θ δ ηphys ηdel ηtype lossRow lossCol ε ζ hI hprov hcontrol
    Δ K Dmatch alpha γ eps βList hF weight w D₀ C hw rhoCorr etaCorr ξClass hηdelEq hηphysEq hηtypeEq h hh DQ mm β εQ Q Hinner hIeq hHeq Small P T₁ σ ρ Y H H₀ HK H' hSmall T τtarget hTargetInterval hTargetInner hTargetCode
    hMarked hOrd hInner hdiv hpres L sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρ₀Host hρ₀Host hDQ hρHostLo hρHostHi hDQhi
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon hBalanceScale κaux κref ζret hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hChangeActual hTypeActual hκauxRet hLossRowEq hLossColEq hFirst
    εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable cap hcap0 hcap hζEq hglobal hrowConcrete hcolConcrete
  have hBase:=long_matching_witness_exact_encoded_reserved_actual_density F G S Del π d r hd hnoshort z M I
  dsimp only at hBase
  obtain ⟨FR,FS,hInterval,hInnerRaw,hCode,hRim,hRimDeg,hSpoke,hSpokeDeg,hDeep,hTypes,hSep,hDiv,hAbs⟩:=
    hBase Pack Enew A R θ δ ηphys ηdel ηtype lossRow lossCol ε ζ hI hprov hcontrol
    Δ K Dmatch alpha γ eps βList hF weight w D₀ C hw rhoCorr etaCorr ξClass hηdelEq hηphysEq hηtypeEq h hh Q Hinner hIeq hHeq T τtarget hTargetInterval hTargetInner hTargetCode
    hMarked hOrd hInner hdiv hpres L sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρ₀Host hρ₀Host hDQ hρHostLo hρHostHi hDQhi
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon hBalanceScale κaux κref ζret hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hChangeActual hTypeActual hκauxRet hLossRowEq hLossColEq hFirst
    εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable cap hcap0 hcap hζEq hglobal hrowConcrete hcolConcrete
  refine ⟨FR,FS,hInterval,hInnerRaw,hCode,hRim,hRimDeg,hSpoke,hSpokeDeg,hDeep,hTypes,hSep,hDiv,hAbs,?_⟩
  intro hdec
  refine long_matching_encoded_factor_reconstruction hEven S G Del hS F hF π d r hd hnoshort z I K θ Dmatch alpha γ eps Δ βList weight w D₀ C M hw
    Pack Enew A R hprov Small ?_ (fun e=>τtarget (Sum.inl e)) T hTargetCode ?_
  · ext e
    have hh:=Finset.ext_iff.mp hSmall e
    simpa only [SimpleGraph.mem_edgeFinset] using hh
  · simpa only [H',Bool.false_eq_true,ite_false,ite_true] using hdec
end Oberwolfach
