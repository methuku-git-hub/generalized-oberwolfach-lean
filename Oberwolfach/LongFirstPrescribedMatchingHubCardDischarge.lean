module

public import Oberwolfach.FirstVortexHubCardinality
public import Oberwolfach.LongFirstPrescribedMatchingFromSamplingLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_prescribed_matchings_from_sampling_law_with_hub_cardinality
    (α lam ε ρ₀ b θ eps ξ:ℝ) (mPath d K:ℕ) (hK:1≤K)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hα:0<α) (hlam:0<lam) (hρ₀:0<ρ₀) (hb:0<b)
    (hαb:α/16≤b) (hbd:b≤((ρ₀/4)/40000)/16) (hmPath:0<mPath)
    (hmarg:4/(mPath:ℝ)≤b/2) (hεsmall:ε≤(ρ₀/4)/80000) (hd:1≤d) (hd3:3≤d):
    ∃N:ℕ,∀(n:ℕ),N≤n→
    ∀ (U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β:ℝ)
      (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (hρhi:initialIndexDensity U Dv≤1)
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

    let u:=2*(∑w:U,(1-(1/100:ℝ)-(1/100:ℝ)/(mPath:ℝ)-
      longAssignedApproxMarkedWeight F hF K mPath θ w-longAssignedApproxOrdinaryWeight F hF K mPath θ w))/(Dv:ℝ)
    ∀ (C₀ a γ δ:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤γ→a≤lam/(10*d)→γ≤lam/(10*d)→
    (∀x,(Del.degree x:ℝ)≤δ)→δ≤ξ*n→
    (∀v∈I,|(((P.neighborFinset v∩I).filter (fun w=>(σ (Sum.inl s(v,w))).1=4)).card:ℝ)-
      u*(P.neighborFinset v∩I).card|<(n:ℝ)^(3/4:ℝ))→
    (∀i,((longRawIncidenceSet S i\matchSet.biUnion
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)))).card:ℝ)≤
      max (a*n) (γ*(longRawIncidenceSet S i).card))→
    ∀Pack:Finset (Sym2 (Fin n)),Pack⊆Used.edgeFinset→Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset→
    ∀(t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
      (Old:U→Finset (Fin n)),
    (∀w,Disjoint (rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w) (Old w))→
    let ρ:ℝ:=ρ₀/4
    P.IsRegularOfDegree Dv→(n:ℝ)/2≤Dv→ρ₀ ≤ initialIndexDensity U Dv→
    (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>σ (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))→
    (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>σ (Sum.inr e)) v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/(mPath:ℝ)+4*(n:ℝ)^(3/4:ℝ))→
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
  obtain ⟨N,hN⟩:=long_first_prescribed_matchings_from_sampling_law_and_event α lam ε ρ₀ b θ eps ξ mPath d K hK hepsAssign hξ hα hlam hρ₀ hb hαb hbd hmPath hmarg hεsmall hd hd3
  refine ⟨max N 1,?_⟩
  intro n hn U C _ _ _ _ P Del Dv m β F hF hρhi Q π D σ g j R raw T S f q φ matchSet Used I P₀ Sel M u C₀ a γ δ hθ hθhi he hC hehi hlamhi hγ haD hγD hDel hδ hrow hmatch Pack hPack hLayer t Jret Old hOld ρ hreg hD hrlo hpair hOcc
  have hNn:N≤n:=le_trans (le_max_left _ _) hn
  have hnpos:0<n:=by omega
  have hDpos:0<Dv:=by
    have hnR:(0:ℝ)<n:=by exact_mod_cast hnpos
    have hDR:(0:ℝ)<Dv:=by linarith
    exact_mod_cast hDR
  have hCardU:=first_vortex_hub_cardinality_le_host hreg hnpos hDpos hρhi
  exact hN n hNn U C P Del Dv m β F hF hρhi Q π D σ g j R matchSet C₀ a γ δ
    hθ hθhi he hC hehi hlamhi hγ hCardU haD hγD hDel hδ hrow hmatch Pack hPack hLayer t Jret Old hOld hreg hD hrlo hpair hOcc
end Oberwolfach
