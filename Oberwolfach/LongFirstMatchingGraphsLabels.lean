module

public import Oberwolfach.ReservedMatchingLabelsFirstVortex
public import Oberwolfach.LongFirstRequiredReservedGraphs
public import Oberwolfach.InnerReservedGraph
public import Oberwolfach.LongFirstRequiredGraphFromEvent
public import Oberwolfach.LongRequiredExtendedHost
public import Oberwolfach.LongRequiredRowsFromCommonIncidence
public import Oberwolfach.LongApproximateUnusedFromCommonIncidence
public import Oberwolfach.LongApproximateResidualAfterDeletion
public import Oberwolfach.LongRequiredVortexRowMargins

@[expose] public section
/-! The existing first-vortex required-graph bounds from a matching selected
after a later physical rim deletion, with its realised degree loss retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_matching_graphs_and_labels_from_event
    (α lam:ℝ) (hα:0<α) (hlam:0<lam) (d:ℕ) (hd:1≤d):
    ∃N:ℕ,∀(n:ℕ),N≤n→
    ∀ (U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β ε:ℝ)
      (Q:Vortex U P Dv β ε m) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
      (g j:Bool) (R:C→Finset (LongRawHubResource n U)),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j Del.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀matchSet:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (matchSet.map q)
    let I:=Q.extendedVertices 1
    let P₀:=longPhysicalStateGraph P σ {0,1,2,3,4}\Used
    let Sel:=longSelectedPhysicalGraph P π d σ
    let M:=fun x y=>Used.Adj x y

    ∀ (θ C₀ u a γ δ:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤u→u≤2*θ→0≤γ→Fintype.card U≤n→2*max a (4*γ)≤lam/3→
    (∀x,(Del.degree x:ℝ)≤δ)→δ≤(lam/3)*n→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(n:ℝ)^(3/4:ℝ))→
    (∀i,((longRawIncidenceSet S i\matchSet.biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀Pack:Finset (Sym2 (Fin n)),Pack⊆Used.edgeFinset→
    ∀(t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
      (Old:U→Finset (Fin n)),
    (∀w,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w) (Old w))→
    ∀ρ mAbs b:ℝ,0≤ρ→ρ*n≤Fintype.card U→ε≤ρ/80000→(n:ℝ)^(3/4:ℝ)≤ρ*n/80000→
    (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))→
    0<mAbs→0≤b→4/mAbs≤b/2→4*(n:ℝ)^(3/4:ℝ)≤b*n/2→
    (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>σ (Sum.inr e)) v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/mAbs+4*(n:ℝ)^(3/4:ℝ))→
    (∀v,((longRequiredPhysicalGraph P P₀ Sel π d I D M).degree v:ℝ)≤(α/16)*n) ∧
    ((longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset.card:ℝ)≤
      (θ*ε^2+lam*ε)*(n:ℝ)^2+24*d*n ∧
    Disjoint (longRequiredPhysicalGraph P P₀ Sel π d I D M).edgeFinset Pack ∧
    let Kbad:=longRequiredPhysicalGraph P P₀ Sel π d I D M
    let Jbad:=spanningRestriction (P\Used) I\Kbad
    (∀v,(Jbad.degree v:ℝ)≤ε*n) ∧ Disjoint Kbad.edgeFinset Jbad.edgeFinset ∧
      Disjoint Used.edgeFinset Jbad.edgeFinset ∧
    let inner:=Q.extendedIndices 1
    let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>σ (Sum.inr e))) inner
    let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>σ (Sum.inr e)) t Jret w)
    (∀e,Disjoint (Lbad e) inner) ∧
    (∀w e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old w→w∈Lbad e→w∈Bad v) ∧
    (∀e∈Kbad.edgeFinset,(ρ/40000)*n≤((Lbad e).card:ℝ)) ∧
    (∀v,((Bad v).card:ℝ)≤b*n) :=by
  obtain ⟨N,hN⟩:=long_first_required_and_reserved_graphs_from_event α lam hα hlam d hd
  refine ⟨N,?_⟩
  intro n hn U C _ _ _ _ P Del Dv m β ε Q π D σ g j R raw T S f q φ matchSet Used I P₀ Sel M θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU hmax hDel hδ hrow hmatch Pack hPack t Jret Old hOld ρ mAbs b hρ hUlo hεsmall herror hpair hmAbs hb hM hNabs hOcc
  obtain ⟨hdegree,hedges,hdis,hJ,hKJ,hUsedJ⟩:=hN n hn U C P Del Dv m β ε Q π D σ g j R matchSet
    θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU hmax hDel hδ hrow hmatch Pack hPack
  let Kbad:=longRequiredPhysicalGraph P P₀ Sel π d I D M
  have hlabels:=reserved_matching_labels_at_first_vortex_level π d (fun e=>σ (Sum.inr e)) t Jret P Dv m β ε Q he Old hOld Kbad ρ hρ hUlo hεsmall herror hpair mAbs b hmAbs hb hCardU hM hNabs hOcc
  exact ⟨hdegree,hedges,hdis,hJ,hKJ,hUsedJ,hlabels⟩
end Oberwolfach
