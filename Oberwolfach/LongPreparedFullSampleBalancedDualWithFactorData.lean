module

public import Oberwolfach.LongMatchedFullSampleBalancedDualWithFactorData
public import Oberwolfach.LongMatchedFullSampleBalancedDualCorrection
public import Oberwolfach.FirstVortexClassPreparedFullPackingGlobal
public import Oberwolfach.LongMatchedClassFullPackingHostGeometry
public import Oberwolfach.FirstVortexClassFullPackingHostAvoidReserve
public import Oberwolfach.LongMatchedHostBalancedDualCorrection
public import Oberwolfach.LongClassWitnessDynamicSameBalancedResidual
public import Oberwolfach.LongMatchedSameBalancedDualCorrection
public import Oberwolfach.LongSameBalancedPhysicalResidual
public import Oberwolfach.LongSameSampleResidualDivisibility
public import Oberwolfach.LongWitnessClassRepairedInnerHostEncoding
public import Oberwolfach.LongMatchedRequiredPackingReady
public import Oberwolfach.LongMatchedClassDynamicHostCompletionReady
public import Oberwolfach.LongMatchedDualUsedEventual

@[expose] public section
/-! The corrected type partition and the completed old/prescribed packing
are obtained on one sample, with the same class orientation and matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance matchedPreparedFullSampleFactorDataFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) matchedPreparedFullSampleFactorDataSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance matchedPreparedFullSampleFactorDataArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_prepared_full_sample_balanced_dual_with_factor_data
    (d e r:ℕ) (ρ₀ rho ζ δLoss εInner eta:ℝ)
    (hρ₀:0<ρ₀) (hrho:0<rho) (heta:0<eta) (hetaR:eta≤rho)
    (hbudget:ζ+δLoss<eta) (hsupply:rho+ζ+δLoss+εInner<ρ₀/(400*((r+4:ℕ):ℝ))):
    ∃N:ℕ,∀n:ℕ,N≤n→∀ [Nonempty (Fin n)] (U:Type) [Fintype U] [DecidableEq U]
    (K D:ℕ) (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D) (hD:0<D) (hd:0<d)
    (hρlo:ρ₀ ≤ initialIndexDensity U D) (hDlo:(n:ℝ)/2≤D)
    (π:Equiv.Perm (Fin n)) (z:MarkedExpandedActualOutcome (U:=U) π d) (I:Finset (Fin n))
    (θ Dmatch alpha γ eps βList:ℝ) (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (weight:(Fin (r+4+1)→Fin n)→ℝ) (w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (D₀:MarkedReferenceDeletion G π d (fun x=>rawExpandedMarkedCollapse x (z.1 x)))
    (C:Finset (Finset (Fin n)⊕(Fin n×U))) (S Del:SimpleGraph (Fin n)) (Mhost:Fin n→Fin n→ℕ)
    (hw:LongClassMatchingDeletionWitness ζ G π d r z I K θ Dmatch alpha γ eps βList F hF weight w D₀ C S Mhost Del)
    (hI:∀v,π v∈I↔v∈I)
    (hclass:∀x∈I,∀y∈I,(longSelectedPhysicalGraph G π d z.1).Adj x y→S.Adj x y)
    (hreserve:markedResourceRimGraph C≤longSelectedPhysicalGraph G π d z.1)
    (hU:0<Fintype.card U)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun x=>rawExpandedApproximateCollapse (Sum.inr x) (z.1 (Sum.inr x))) false)
      (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hd2:2≤d)
    (H:Finset U) (absorber:U→Finset (Fin n)) (δlocal ρstep δglobal:ℝ)
    (hLossScale:5*Real.sqrt δglobal≤δLoss)
    (εQ lamAssign αAssign b βpre βfinal ρreserve:ℝ)
    (hρstep:0<ρstep) (hb:0≤b) (hbsmall:b≤((ρstep/4)/40000)/16) (hαb:αAssign/16≤b)
    (hθδ:10*θ≤δglobal) (hεδ:εQ≤δglobal) (hβ:0<βfinal) (hβ1:βfinal≤1)
    (hδ:0<δglobal) (hδbound:δglobal≤(βfinal/100)^2)
    (hn0:0<n) (hnβ:100/βfinal≤(n:ℝ)) (hnδ:2/Real.sqrt δglobal≤(n:ℝ)) (hu:Fintype.card U≤n)
    (hρreserve:0≤ρreserve) (hCreserve:(C.card:ℝ)≤ρreserve*n) (hListMargin:βfinal+2*ρreserve≤βpre)
    (mm:ℕ) (β ξ a:ℝ) (Vort:Vortex U G D β εQ mm)
    (hIeq:I=Vort.extendedVertices 1) (hHeq:H=Vort.extendedIndices 1) (hζξ:ζ≤ξ)
    (hPrepared:FirstVortexClassPreparedFullPackingOutcomeWithGlobalLoad G S π D mm d (r+4) β εQ Vort F hF θ lamAssign eps δlocal δglobal (αAssign/2) b ρstep ξ ζ a γ weight w z.1
      (startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) Jret),
    let t:=startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedApproximateCollapse x (z.1 x)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀(X:Finset (Fin n)) (Z:Finset U),
    MarkedFixedTerminalAbsorber G π d (r+4) (fun e=>rawExpandedMarkedCollapse e (z.1 e))
      (retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t Jret false false) C X Z→
    (∀w,IsExtendingList (fun x y=>rawSelectedPhysicalRelation G π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
      (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w\(I∪retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t Jret w)) βpre)→
    (I.card:ℝ)≤εInner*n→C.card≤e→∀p₂ k₂ u:ℝ,
    (∀v,|((rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false v).card:ℝ)-
      (∑w,longAssignedIntervalProbability F hF K (r+4) θ w false/(d:ℝ))|<(n:ℝ)^(3/5:ℝ))→
    (∀j v,|((∑x,sampledColourOrientation G (fun x=>z.1 (Sum.inl x)) j x v:ℕ):ℝ)-
      markedExpandedPhysicalProbability (initialIndexDensity U D*(1/100:ℝ)/2) (initialIndexDensity U D*((1/100:ℝ)/((r+4:ℕ):ℝ))/2) p₂ k₂ u j/2*G.degree v|<(n:ℝ)^(3/5:ℝ))→
    ∃(Pack:Finset (Sym2 (Fin n))) (E:U→Finset (Sym2 (Fin n))) (Spokes:U→Finset (Fin n)),
      let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔prescribedPhysicalUnion E
      let P:=longEligibleResidualArc Mhost Small ⊥
      let T₁:=longDualInitialMarked G (fun x=>z.1 (Sum.inl x)) Mhost Small (longOrdinaryArcEligible π d) (longMarkedArcEligible π d);
      ∃T:Finset {x:(Fin n)×(Fin n) // P x},
      (∀x y,Small.Adj x y→¬(markedResourceRimGraph C).Adj x y) ∧
      (∀v,directedInCount P T v=d*startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false)) ∧
      (∀x∈T,longMarkedArcEligible π d x.val) ∧ (∀x,x∉T→longOrdinaryArcEligible π d x.val) ∧
      (∀x,x.val.1∈I→(x∈T↔x∈T₁)) ∧
      (∀x,Sum.inl ({x.val.1,x.val.2}:Finset (Fin n))∈C→(x∈T↔x∈T₁)) ∧
      (∀v,((physicalEdgeGraph (changedDirectedPhysicalEdges P T T₁)).degree v:ℝ)≤(1+2/rho)*eta*n+(n:ℝ)^(3/5:ℝ)) ∧
      (∀mark a b,a∈I→b∈I→
        (markedPhysicalRim G π (3*d) (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) mark a b=1 ↔
          if mark then ∃e:residualMarkedArc P T,e.val.val.1=a∧π.symm e.val.val.2=b
          else ∃e:residualOrdinaryArc P T,e.val.val.1=a∧e.val.val.2=b)) ∧
      let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun x=>raw (Sum.inr x)) false t Jret w=>d) Subtype.val
      let H₀:=fun v w=>v∈Spokes w\Y w
      MarkedRemainderDivisible
        (fun x:residualOrdinaryArc P T=>x.val.val.1) (fun x=>x.val.val.2)
        (fun x:residualMarkedArc P T=>x.val.val.1) (fun x=>π.symm x.val.val.2)
        (retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false true true) Finset.univ
        (Finset.univ.filter (fun z:(Fin n)×U=>H₀ z.1 z.2∨retainedRawMarkedSpokes π d (fun x=>raw (Sum.inr x)) false t Jret false true true z.1 z.2)) (r+4) ∧
      ∃A:Finset (Fin n×Fin n),Small.edgeFinset=A.image (fun a=>s(a.1,a.2)) ∧
        (∀a∈A,Mhost a.1 a.2=1) ∧
        LongFactorComplementProvenance F S G π d (r+4) raw t Jret Pack E A Spokes :=by
  obtain ⟨N,hN⟩:=long_matched_full_sample_balanced_dual_with_factor_data d e r ρ₀ rho ζ δLoss εInner eta hρ₀ hrho heta hetaR hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ K D G hreg hD hd hρlo hDlo π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw hI hclass hreserve hU Jret hnoshort hd2 H absorber δlocal ρstep δglobal hLossScale εQ lamAssign αAssign b βpre βfinal ρreserve hρstep hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn0 hnβ hnδ hu hρreserve hCreserve hListMargin mm β ξ a Vort hIeq hHeq hζξ hPrepared t raw ℓ R Tmix Q q φ X Z habs hext hcard hC p₂ k₂ u hstarts hdegrees
  subst I
  subst H
  have hDel:∀v,(Del.degree v:ℝ)≤ζ*n:=hw.2.2.2.2.2.1
  have hξDel:ζ*n≤ξ*n:=mul_le_mul_of_nonneg_right hζξ (Nat.cast_nonneg n)
  unfold FirstVortexClassPreparedFullPackingOutcomeWithGlobalLoad at hPrepared
  obtain ⟨Mix,hpos,hdis,hinc,hlow,hup,hcount,hsource⟩:=hPrepared Del (ζ*n) hDel le_rfl hξDel
  let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) true x (π.symm y)≠1
  obtain ⟨hU',hGlobal⟩:=hsource Req absorber C X Z habs
  have hN':=hN n hn
  have hdec:matchedFullSampleFactorDataFin n=matchedPreparedFullSampleFactorDataFin n:=Subsingleton.elim _ _
  have hdecK:matchedFullSampleFactorDataFin K=matchedPreparedFullSampleFactorDataFin K:=Subsingleton.elim _ _
  try rw [hdec] at hN'
  try rw [hdecK] at hN'
  apply hN' U K D G hreg hD hd hρlo hDlo π z (Vort.extendedVertices 1) θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw hI hclass hreserve hU Jret hnoshort hd2 (Vort.extendedIndices 1) absorber δlocal ρstep δglobal hLossScale εQ lamAssign αAssign b βpre βfinal ρreserve hρstep hb hbsmall hαb hθδ hεδ hβ hβ1 hδ hδbound hn0 hnβ hnδ hu hρreserve hCreserve hListMargin Mix hext ?_ hcard hC p₂ k₂ u hstarts hdegrees
  simpa only [Req,longRawHubResources,longRawHubCandidates,show (2:ℝ)*(αAssign/2)=αAssign by ring] using hGlobal
end Oberwolfach
