module

public import Oberwolfach.LongSameBalancedPhysicalResidualWithFactorDataExact
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
local instance matchedSameBalancedFactorDataExactFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
local instance (priority := 2000) matchedSameBalancedFactorDataExactSix : DecidableEq (Fin 6) := instDecidableEqFin 6
local instance matchedSameBalancedFactorDataExactArc {n:ℕ} (P:(Fin n×Fin n)→Prop):DecidableEq {e:Fin n×Fin n // P e}:=Classical.decEq _
attribute [local instance] partitionedDivisibleArcFinite partitionedDivisibleOrdFinite partitionedDivisibleMarkFinite

theorem long_matched_same_balanced_dual_correction_with_factor_data_exact
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
    (hU:0<Fintype.card U) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun x=>rawExpandedApproximateCollapse (Sum.inr x) (z.1 (Sum.inr x))) false) t)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ht:t=startRetentionMinimum (rawStartHubSet π d (fun x=>z.1 (Sum.inr x)) false))
    (H:Finset U) (absorber:U→Finset (Fin n)) (δlocal ρstep δglobal:ℝ)
    (hLossScale:5*Real.sqrt δglobal≤δLoss)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun x=>rawExpandedApproximateCollapse x (z.1 x)
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d (r+4) ℓ)
    let Tmix:=bernoulliVertexSet (longRawHubState G π d raw true true)
    let Q:=longRawSurvivingResources G π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R Q Tmix (long_raw_surviving_resources_subset G π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding G π d raw true true;
    ∀Mix:Finset (RestrictedResource R (Function.Embedding.subtype (·∈Q))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)
    let Sel:=longSelectedPhysicalGraph G π d z.1
    let Req:=fun x y=>Mhost x y=1 ∧ markedPhysicalRim G π (3*d)
      (fun x=>markedExpandedPhysicalCollapse (z.1 (Sum.inl x))) true x (π.symm y)≠1
    let Kbase:=longRequiredPhysicalGraph S (S\Used) Sel π d I Req (fun x y=>Used.Adj x y)
    let Kplus:=fun Pack:Finset (Sym2 (Fin n))=>longClassInnerRequiredRepair S Used Kbase I Pack
    let DelPlus:=Del⊔markedResourceRimGraph C;
    LongSelectedClassDynamicSourceSameBalanced hU F G π d (r+4) ℓ raw t Jret z.1 H I S Kplus Used DelPlus (markedResourceRimGraph C) absorber δlocal Mhost (fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y) Extra ρstep θ δglobal (Mix.map q)→
    (∀occupied Pack,Extra occupied Pack→Pack=Used.edgeFinset)→
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
      Pack=Used.edgeFinset ∧ Pack⊆(longApproximatePhysicalGraph G π d z.1).edgeFinset ∧
      (∀v,((prescribedPhysicalUnion E).degree v:ℝ)≤5*Real.sqrt δglobal*Fintype.card (Fin n)) ∧
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
  obtain ⟨N,hN⟩:=long_matched_dual_used_eventual_correction d e (r+4) ρ₀ rho ζ δLoss εInner eta hρ₀ (by omega) hrho heta hetaR hbudget hsupply
  refine ⟨N,?_⟩
  intro n hn _ U _ _ K D G hreg hD hd hρlo hDlo π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Mhost hw hI hclass hreserve hU t Jret hnoshort ht H absorber δlocal ρstep δglobal hLossScale Extra raw ℓ R Tmix Q q φ Mix Used Sel Req Kbase Kplus DelPlus hsource hPackEq hcard hC p₂ k₂ u hstarts hdegrees
  have hdis:Disjoint Sel Used:=by
    have hdis0:=long_used_sampled_matching_avoids_selected G π d z.1 true true
      (restrictedResourceSet R (Function.Embedding.subtype (·∈Tmix))) (Mix.map q)
    convert hdis0 using 1 <;> congr! 5 <;> exact Subsingleton.elim _ _
  have hbalanced:=long_same_balanced_physical_residual_with_factor_data_exact hU F hF G π d (r+4) ℓ raw t Jret z.1 H I Kplus Used DelPlus (markedResourceRimGraph C) absorber δlocal S Mhost
    (fun x y=>Mhost x y=1 ∧ ¬(markedResourceRimGraph C).Adj x y) Extra ρstep θ δglobal (fun x y h=>h.1) hw.1 hPackEq
  have hdec0:sameBalancedPhysicalFactorDataExactFin n=matchedSameBalancedFactorDataExactFin n:=Subsingleton.elim _ _
  have hdec0K:sameBalancedPhysicalFactorDataExactFin K=matchedSameBalancedFactorDataExactFin K:=Subsingleton.elim _ _
  try rw [hdec0] at hbalanced
  try rw [hdec0K] at hbalanced
  obtain ⟨Pack,E,A,Spokes,hPackEqResult,hUsed,hApprox,hcover,hJ,hdegree,hSmall,hA,hDeg,hSpokes,hSafe,hFactor⟩:=hbalanced (Mix.map q) hsource
  have hbase:Kbase.edgeFinset⊆Finset.univ.biUnion E:=by
    intro x hx
    apply hcover
    apply SimpleGraph.edgeFinset_mono (show Kbase≤Kplus Pack from le_sup_left)
    exact hx
  have hready0:=long_matched_required_packing_ready ζ G π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Sel Mhost hw
  have hdec1:instDecidableEqFin n=matchedSameBalancedFactorDataExactFin n:=Subsingleton.elim _ _
  have hdec1K:instDecidableEqFin K=matchedSameBalancedFactorDataExactFin K:=Subsingleton.elim _ _
  try rw [hdec1] at hready0
  try rw [hdec1K] at hready0
  have hready:=hready0 Mix Pack E hbase
  let Loss:=prescribedPhysicalUnion E
  let Small:=SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 (Fin n)))⊔Loss
  have hLoss:∀v,(Loss.degree v:ℝ)≤δLoss*n:=by
    intro v
    have hn0:(0:ℝ)≤n:=by positivity
    have hh:=mul_le_mul_of_nonneg_right hLossScale hn0
    have hd':(Loss.degree v:ℝ)≤5*Real.sqrt δglobal*n:=by
      simpa only [Loss,Fintype.card_fin] using hdegree v
    exact hd'.trans hh
  have hN':=hN n hn
  have hdec2:matchedDualUsedFin n=matchedSameBalancedFactorDataExactFin n:=Subsingleton.elim _ _
  have hdec2K:matchedDualUsedFin K=matchedSameBalancedFactorDataExactFin K:=Subsingleton.elim _ _
  try rw [hdec2] at hN'
  try rw [hdec2K] at hN'
  obtain ⟨T,hcount,hmark,hord,hinner,hreserveT,hchange⟩:=hN' U r K D G hreg hD hd hρlo hDlo π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Small Loss Mhost hw Pack hApprox (le_refl _) Used hready.1 hready.2 hLoss hcard hC p₂ k₂ u hstarts hdegrees
  have hagree:=long_witness_class_repaired_inner_host_encoding ζ G π z I θ Dmatch alpha γ eps βList F hF weight w D₀ C S Del Used Mhost hw Pack E hI hclass hdis hUsed hJ hcover T hinner
  have hcount':∀v,directedInCount (longEligibleResidualArc Mhost Small ⊥) T v=d*t:=by
    intro v
    rw [ht]
    exact hcount v
  letI : DecidableRel Small.Adj := fun x y=>Classical.propDecidable _
  have hSmall':@SimpleGraph.edgeFinset (Fin n) Small Small.fintypeEdgeSet=A.image (fun a=>s(a.1,a.2)):=by
    convert hSmall using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  have hdiv:=long_same_sample_residual_divisibility S Small Mhost A hw.1 hA hSmall' π d (r+4) (by omega)
    (by intro x l hl hld; exact hnoshort x l hl (by omega)) (fun x=>raw (Sum.inr x)) false true t Jret Spokes
    (fun w=>(hSpokes w).1) (fun w=>(hSpokes w).2) hDeg T hcount'
  exact ⟨Pack,E,Spokes,T,hPackEqResult,hApprox,hdegree,hSafe,hcount,hmark,hord,hinner,hreserveT,hchange,hagree,hdiv,A,hSmall,hA,hFactor⟩
end Oberwolfach
