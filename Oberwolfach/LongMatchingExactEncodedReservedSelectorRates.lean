module

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
local instance exactEncodedSelectorRatesFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n
local instance exactEncodedSelectorRatesArc {n:ℕ} (P:Fin n×Fin n→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite
theorem long_matching_witness_exact_encoded_reserved_selector_rates
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (F:U→SimpleGraph (Fin n)) (G S Del:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d r:ℕ)
    (hd:2≤d) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (M:Fin n→Fin n→ℕ) (I:Finset (Fin n)):
    let m:=r+4
    let ω:=z.1
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (ω e)
    let t:=startRetentionMinimum (rawStartHubSet π d (fun e=>ω (Sum.inr e)) false)
    let J:=z.2;
    ∀ (Pack:Finset (Sym2 (Fin n))) (Enew:U→Finset (Sym2 (Fin n))) (A:Finset (Fin n×Fin n))
    (R:U→Finset (Fin n)) (θ δ ηphys ηdel ηtype lossRow lossCol ε ζ:ℝ)
    (hI:∀v,π v∈I↔v∈I)
    (hprov:LongFactorComplementProvenance F S G π d m raw t J Pack Enew A R)
    (hcontrol:LongResidualSpokeCompletionControl π d raw t J R θ δ)
    (Δ:ℝ) (K:ℕ) (Dmatch alpha γ eps βList:ℝ)
    (hF:∀u,(F u).IsRegularOfDegree 2) (weight:(Fin (r+4+1)→Fin n)→ℝ)
    (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (z.1 e)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U)))
    (hw:LongClassMatchingDeletionWitness Δ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S M Del)
    (hDelBound:Δ*n≤ηdel)
    (h:ℕ) (hh:1≤h)
    {DQ mm:ℕ} {β εQ:ℝ} (Q:Vortex U G DQ β εQ mm) (Hinner:Finset U)
    (hIeq:I=Q.extendedVertices 1) (hHeq:Hinner=Q.extendedIndices 1),
    let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion Enew
    let P:=longEligibleResidualArc M Small ⊥
    let T₁:=longDualInitialMarked G (fun e=>ω (Sum.inl e)) M Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d)
    let σ:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (ω e)
    let ρ:=fun e=>raw (Sum.inr e)
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d ρ false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d ρ false t J false false
    let H₀:=fun v w=>v∈R w\Y w
    let HK:=retainedRawMarkedSpokes π d ρ false t J false true true
    let H':Bool→Fin n→U→Prop:=fun b v w=>if b then HK v w else H₀ v w;
    ∀T:Finset {e:Fin n×Fin n // P e},
    ∀(τtarget:RawMarkedOutcome (Fin n) U Bool Bool),
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
      (Finset.univ.filter (fun z:Fin n×U=>H₀ z.1 z.2∨HK z.1 z.2)) m→
    ∀(hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (L sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon:ℕ)
      (ρHost:ℝ) (hρHost:0<ρHost) (hsizeHost:ρHost*DQ=2*Fintype.card U)
      (βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
        εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
        ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance:ℝ)
      (hγRich:0≤γRich)
      (levelWeight:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
      (hCommon:LongMatchingCommonEvent G π DQ mm β εQ Q hpres r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h
        F hF θ ρHost βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent
        εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent
        ρ₀Event sstarEvent kstarEvent τLevelEvent levelWeight (markedExpandedActualSelected π d z))
      (hBalanceScale:ε=ηBalance*n)
      (κaux κref:ℝ) (hηBalance:0<ηBalance) (hκaux:0<κaux) (hκref:0≤κref) (hκrefCap:κref≤κaux)
      (hεRefEq:εRefEvent=κref/4) (hεNbr0:0≤εNbrEvent) (hεNbrCap:εNbrEvent≤κaux)
      (hκauxCap:κaux≤ηBalance/(8*((((r+4):ℕ):ℝ)+1))) (hUcard:Fintype.card U≤n),
    (∀v,((changed ((longSelectedPhysicalGraph G π d ω).neighborFinset v) ((S\Small).neighborFinset v)).card:ℝ)≤ηphys)→
    (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤ηtype)→
    (∀v,((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossRow)→
    (∀w,((Finset.univ.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤lossCol)→
    2*(lossRow+(δ*n+(Real.sqrt δ*n+1)))+(ε+2*(ηphys+ηdel+ηtype))≤ζ*n→
    2*(lossCol+10*θ*n)+ε≤ζ*n→
    (∀w∈Hinner,∀v∈I,v∈R w\Y w↔H false v w)→
    ∀ (εStable ζStable capStable:ℝ) (sizeStable aStable bStable eStable fStable:ℕ),
    0≤ζStable→
    MarkedRetainedRobustChangeEvent G π d r false false εStable ζStable capStable sizeStable aStable bStable eStable fStable ⟨σ,J⟩→
    ηphys+ηdel+ηtype≤capStable*n→ζ≤capStable→
    ∃(FR:SimpleGraph (Fin n)) (FS:SimpleGraph (Fin n⊕U)),
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
      let Sp:=Finset.univ.filter (fun p:Fin n×U=>H' false p.1 p.2∨H' true p.1 p.2)
      let E:=MarkedSampleArc G π (3*d) (fun e=>τtarget (Sum.inl e)) false
      let K:=MarkedSampleArc G π (3*d) (fun e=>τtarget (Sum.inl e)) true;
      MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ Sp (r+4) ∧
      MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H' false) (H' true) π (3*d) r sizeStable aStable bStable eStable fStable εStable :=by
  intro m ω raw t J Pack Enew A R θ δ ηphys ηdel ηtype lossRow lossCol ε ζ hI hprov hcontrol
    Δ K Dmatch alpha γ eps βList hF weight w D₀ C hw hDelBound h hh DQ mm β εQ Q Hinner hIeq hHeq Small P T₁ σ ρ Y H H₀ HK H' T τtarget hTargetInterval hTargetInner hTargetCode
    hMarked hOrd hInner hdiv hpres L sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon ρHost hρHost hsizeHost
    βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance hγRich levelWeight hCommon hBalanceScale κaux κref hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap hUcard hChange hType hRetRow hRetCol hBudgetRow hBudgetCol hFirst
    εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable hRimCap hSpokeCap
  obtain ⟨_,_,hGlobalBudget⟩:=marked_common_selector_global_balance_budget r ηBalance κaux κref εRefEvent εNbrEvent
    hηBalance hκaux hκref hκrefCap hεRefEq hεNbr0 hεNbrCap hκauxCap
  obtain ⟨hCommonBudget,hCommonMarked,hCommonColumn⟩:=hGlobalBudget n U hUcard
  have hn:1≤n:=by
    have hh':0<Fintype.card (Fin n):=Fintype.card_pos
    simp only [Fintype.card_fin] at hh'
    omega
  have hbal:MarkedRestrictedBalanceWithSpokes G π d m Finset.univ Finset.univ ε σ H:=by
    have hb:=marked_long_common_agreement_full_restricted_balance hn G π DQ mm β εQ Q hpres
      r K d sizeCommon aCommon bCommon eCommon aRob bRob eRob fCommon L h hh F hF θ ρHost hρHost hsizeHost
      βCommonEvent βCommonRef εAbsEvent εRobEvent ζRobEvent εRefEvent δRefEvent γRich tstarEvent ζEvent εBalEvent ζBalEvent εNbrEvent ζNbrEvent BloadEvent εLoadEvent ζLoadEvent ζLocalEvent ζConfigEvent ρ₀Event sstarEvent kstarEvent τLevelEvent ηBalance
      hγRich levelWeight (markedExpandedActualSelected π d z) hCommon hCommonBudget hCommonMarked hCommonColumn
    rw [hBalanceScale]
    convert hb using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
  obtain ⟨τref,FR,FS,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩:=
    long_matching_witness_vortex_graphs_minimal_balance F G S Del π d r hd hnoshort z M I Pack Enew A R
      θ δ ηphys ηdel ηtype lossRow lossCol ε ζ hI hprov hcontrol Δ K Dmatch alpha γ eps βList hF weight w D₀ C hw hDelBound Q Hinner hIeq hHeq T
      hMarked hOrd hInner hdiv hbal hChange hType hRetRow hRetCol hBudgetRow hBudgetCol hFirst
  have hFR:∀v,(FR.degree v:ℝ) ≤ capStable*Fintype.card (Fin n):=by
    intro v
    simpa only [Fintype.card_fin] using (h5 v).trans hRimCap
  have hFS:∀v,(FS.degree v:ℝ) ≤ capStable*Fintype.card (Fin n):=by
    intro v
    have hm:=mul_le_mul_of_nonneg_right hSpokeCap (show (0:ℝ) ≤ n by positivity)
    simpa only [Fintype.card_fin] using (h7 v).trans hm
  have hnew:=long_same_residual_encoded_change_and_robust_transfer G S Small π d r ⟨σ,J⟩
    εStable ζStable capStable sizeStable aStable bStable eStable fStable hζStable hstable
    τref τtarget H' FR FS h4 h6 hFR hFS h9 M T h3 hTargetCode
  have hdiv':MarkedRemainderDivisible
      (fun e:residualOrdinaryArc P T=>e.val.val.1) (fun e=>e.val.val.2)
      (fun e:residualMarkedArc P T=>e.val.val.1) (fun e=>π.symm e.val.val.2)
      (H' true) Finset.univ
      (Finset.univ.filter (fun p:Fin n×U=>H' false p.1 p.2∨H' true p.1 p.2)) (r+4):=by
    simpa only [H',Bool.false_eq_true,if_false,if_true,m] using hdiv
  have hnew':=hnew (by convert hdiv' using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)
  have hspoke:∀b v u,v∈Q.extendedVertices 1 → u∈Q.extendedIndices 1 → (H b v u↔H' b v u):=by
    intro b v u hv hu
    cases b with
    | false =>
      have hh:=hFirst u (by simpa only [hHeq] using hu) v (by simpa only [hIeq] using hv)
      simpa only [H',Bool.false_eq_true,if_false,H₀] using hh.symm
    | true => simp only [H',if_true,HK,H,retainedRawMarkedSpokes]
  have hdeep:=marked_vortex_protected_deeper_equality Q σ τtarget H H'
    (by intro e he;exact (hTargetInner e (by simpa only [hIeq] using he)).symm)
    (by intro e;exact (hTargetInterval e).symm) hspoke
  refine ⟨FR,FS,hTargetInterval,hTargetInner,hTargetCode,hnew'.1,h5,h6,h7,hdeep,h9,h10,?_⟩
  convert hnew'.2 using 1 <;> congr! 8 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach

