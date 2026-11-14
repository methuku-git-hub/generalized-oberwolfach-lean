module

public import Oberwolfach.FirstVortexDeletionRateMargin
public import Oberwolfach.LongFirstPrescribedNumericalHypotheses
public import Oberwolfach.LongFirstPrescribedMatchingsOrderedRates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_first_prescribed_matchings_from_event_with_deletion_margin_discharged
    (α lam ε ρ₀ b θ eps ξ:ℝ) (mPath d K:ℕ) (hK:1≤K)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hα:0<α) (hlam:0<lam) (hρ₀:0<ρ₀) (hb:0<b)
    (hαb:α/16≤b) (hbd:b≤((ρ₀/4)/40000)/16) (hmPath:0<mPath)
    (hmarg:4/(mPath:ℝ)≤b/2) (hεsmall:ε≤(ρ₀/4)/80000) (hd:1≤d) (hd3:3≤d):
    ∃N:ℕ,∀(n:ℕ),N≤n→
    ∀ (U C:Type) [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
      (P Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β:ℝ)
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

    ∀ (C₀ u a γ δ:ℝ),0≤θ→θ≤1/100→0≤ε→1≤C₀→ε≤α/(1000*C₀)→
    lam≤α/128→0≤u→u≤2*θ→0≤γ→Fintype.card U≤n→a≤lam/(10*d)→γ≤lam/(10*d)→
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
  obtain ⟨N₁,hN₁⟩:=long_first_prescribed_matchings_from_event_with_ordered_rates α lam hα hlam d hd hd3
  obtain ⟨N₂,hN₂⟩:=long_first_prescribed_numerical_hypotheses ρ₀ α b ε mPath hρ₀ hb hαb hbd hmPath hmarg hεsmall
  refine ⟨max (max N₁ N₂) 1,?_⟩
  intro n hn U C _ _ _ _ P Del Dv m β Q π D σ g j R raw T S f q φ matchSet Used I P₀ Sel M C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU haD hγD hDel hδ hrow hmatch Pack hPack hLayer t Jret Old hOld ρ hreg hD hrlo hpair hOcc
  have hN1:N₁≤n:=by omega
  have hN2:N₂≤n:=by omega
  have hnpos:0<n:=by omega
  have hθ1:θ≤1:=by linarith
  have hξlam:=first_vortex_deletion_rate_margin K θ lam eps ξ hK hθ hθ1 hlam.le hepsAssign hξ
  have hδlam:δ≤(lam/3)*(n:ℝ):=by
    exact hδ.trans (mul_le_mul_of_nonneg_right hξlam (Nat.cast_nonneg n))
  obtain ⟨hρ,hαb',hbsmall,hUlo,hεsmall',herror,hmAbs,hb',hM,hNabs⟩:=hN₂ n hN2 hreg hnpos hD hrlo
  exact hN₁ n hN1 U C P Del Dv m β ε Q π D σ g j R matchSet
    θ C₀ u a γ δ hθ hθhi he hC hehi hlamhi hu huhi hγ hCardU haD hγD hDel hδlam hrow hmatch Pack hPack hLayer t Jret Old hOld
    ρ mPath b hρ hαb' hbsmall hUlo hεsmall' herror hpair hmAbs hb' hM hNabs hOcc
end Oberwolfach
