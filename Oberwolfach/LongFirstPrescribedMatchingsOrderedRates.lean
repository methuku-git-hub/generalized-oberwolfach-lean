module

public import Oberwolfach.FirstVortexMatchingIncidenceMargin
public import Oberwolfach.AssignedEdgePreparationShielded
public import Oberwolfach.LongFirstRequiredExtendedHost
public import Oberwolfach.GraphEdgeAssignmentOriginal
public import Oberwolfach.LongFirstMatchingGraphsLabels
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

theorem long_first_prescribed_matchings_from_event_with_ordered_rates
    (α lam:ℝ) (hα:0<α) (hlam:0<lam) (d:ℕ) (hd:1≤d) (hd3:3≤d):
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
    lam≤α/128→0≤u→u≤2*θ→0≤γ→Fintype.card U≤n→a≤lam/(10*d)→γ≤lam/(10*d)→
    (∀x,(Del.degree x:ℝ)≤δ)→δ≤(lam/3)*n→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(n:ℝ)^(3/4:ℝ))→
    (∀i,((longRawIncidenceSet S i\matchSet.biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀Pack:Finset (Sym2 (Fin n)),Pack⊆Used.edgeFinset→Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset→
    ∀(t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
      (Old:U→Finset (Fin n)),
    (∀w,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w) (Old w))→
    ∀ρ mAbs b:ℝ,0<ρ→(α/16)≤b→b≤(ρ/40000)/16→ρ*n≤Fintype.card U→ε≤ρ/80000→(n:ℝ)^(3/4:ℝ)≤ρ*n/80000→
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
    (∀v,((Bad v).card:ℝ)≤b*n) ∧
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ Kbad.Adj x y
    let Kload:=⌈4*(Kbad.edgeFinset.card:ℝ)/((ρ/40000)*n)⌉₊
    ∃(assign:Sym2 (Fin n)→U) (orient:Sym2 (Fin n)→Fin n×Fin n),
      (∀e∈Kbad.edgeFinset,prescribedArcPhysical (orient e)=e ∧ Dstar (orient e).1 (orient e).2) ∧
      (∀e∈Kbad.edgeFinset,assign e∈Lbad e ∧ ∀v∈e.toFinset,assign e∉Bad v) ∧
      (∀e∈Kbad.edgeFinset,∀e'∈Kbad.edgeFinset,e≠e'→assign e=assign e'→Disjoint e.toFinset e'.toFinset) ∧
      (∀w,(Kbad.edgeFinset.filter (fun e=>assign e=w)).card≤Kload) ∧
      (∀w,Disjoint (Old w) (prescribedMatchingEndpoints (prescribedAssignedArcs Kbad assign orient w))) ∧
      (∀w,w∈inner→prescribedAssignedArcs Kbad assign orient w=∅) ∧
      (∀w,IsPrescribedOrientedMatching (prescribedAssignedArcs Kbad assign orient w)) ∧
      (∀w,(prescribedAssignedArcs Kbad assign orient w).card≤Kload) :=by
  obtain ⟨N,hN⟩:=long_first_matching_graphs_and_labels_from_event α lam hα hlam d hd
  refine ⟨max N 1,?_⟩
  intro n hn U C _ _ _ _ P Del Dv m β ε Q π D σ g j R raw T S f q φ matchSet Used I P₀ Sel M θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU haD hγD hDel hδ hrow hmatch Pack hPack hLayer t Jret Old hOld ρ mAbs b hρ hαb hbsmall hUlo hεsmall herror hpair hmAbs hb hM hNabs hOcc
  have hnN:N≤n:=le_trans (le_max_left _ _) hn
  have hmax:=first_vortex_matching_incidence_margin d lam a γ hd3 hlam.le haD hγD
  have hnpos:0<n:=by omega
  letI:Nonempty (Fin n):=⟨⟨0,hnpos⟩⟩
  have hUpos:0<Fintype.card U:=by
    have hh:0<(ρ:ℝ)*n:=mul_pos hρ (by exact_mod_cast hnpos)
    have hr:0<(Fintype.card U:ℝ):=lt_of_lt_of_le hh hUlo
    exact_mod_cast hr
  letI:Nonempty U:=Fintype.card_pos_iff.mp hUpos
  obtain ⟨hdegree,hedges,hdis,hJ,hKJ,hUsedJ,hOutside,hShield,hLabels,hBad⟩:=hN n hnN U C P Del Dv m β ε Q π D σ g j R matchSet
    θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU hmax hDel hδ hrow hmatch Pack hPack t Jret Old hOld ρ mAbs b hρ.le hUlo hεsmall herror hpair hmAbs hb hM hNabs hOcc
  let Kbad:=longRequiredPhysicalGraph P P₀ Sel π d I D M
  let Jbad:=spanningRestriction (P\Used) I\Kbad
  let inner:=Q.extendedIndices 1
  let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d (fun e=>σ (Sum.inr e))) inner
  let Bad:=fun v:Fin n=>Finset.univ.filter (fun w=>v∈retainedFinalMarkedAt π d (fun e=>σ (Sum.inr e)) t Jret w)
  let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
  let Dstar:=fun x y=>Dfree x y ∨ Kbad.Adj x y
  have hG:∀v,(Kbad.degree v:ℝ)≤b*n:=by
    intro v
    have hh:=mul_le_mul_of_nonneg_right hαb (Nat.cast_nonneg n)
    exact (hdegree v).trans hh
  have hαcap:0<ρ/40000:=by positivity
  have hnV:0<Fintype.card (Fin n):=by simpa using hnpos
  obtain ⟨hDD,hDstar,hHost,hPackDis,hFreePack⟩:=long_first_required_extended_host P Del Used π d I σ D Pack hPack hLayer
  obtain ⟨assign,orient,horient,hallowed,hconf,hcap,hold,hinner,hmatching,hcard⟩:=
    prepare_assigned_bad_edges_with_shield Kbad Dstar hDstar Lbad Bad Old inner hShield
      (fun e _=>hOutside e) (ρ/40000) b hαcap hb hbsmall hnV
      (by simpa only [Fintype.card_fin] using hLabels)
      (by simpa only [Fintype.card_fin] using hBad)
      (by simpa only [Fintype.card_fin] using hG)
  refine ⟨hdegree,hedges,hdis,hJ,hKJ,hUsedJ,hOutside,hShield,hLabels,hBad,assign,orient,horient,hallowed,?_,
    by simpa only [Fintype.card_fin] using hcap,hold,hinner,hmatching,by simpa only [Fintype.card_fin] using hcard⟩
  intro e he e' he' hne heq
  exact hconf (assign e) e he e' he' rfl heq.symm hne
end Oberwolfach
