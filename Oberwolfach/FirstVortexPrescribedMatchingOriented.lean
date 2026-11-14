module

public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.LongSelectedOrientedSourceWithLoad
public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.FirstVortexPrescribedAssignmentOutcome
public import Oberwolfach.SelectedHostAvoidsApproximatePacking

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexAttachOrientedSourceFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n
theorem long_first_prescribed_matching_attached_to_oriented_source
    (α lam ε ρ₀ b θ eps ξ:ℝ) (mPath d K:ℕ) (hK:1≤K)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hξ:4*ξ≤eps/2) (hα:0<α) (hlam:0<lam) (hρ₀:0<ρ₀) (hb:0<b)
    (hαb:α/16≤b) (hbd:b≤((ρ₀/4)/40000)/16) (hmPath:0<mPath)
    (hmarg:4/(mPath:ℝ)≤b/2) (hεsmall:ε≤(ρ₀/4)/80000) (hd:1≤d) (hd3:3≤d):
    ∃N:ℕ,∀(n:ℕ),N≤n→
    ∀ (U:Type) [Fintype U] [DecidableEq U]
      (P Del:SimpleGraph (Fin n)) (Dv m:ℕ) (β:ℝ)
      (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
      (hρhi:initialIndexDensity U Dv≤1)
      (Q:Vortex U P Dv β ε m) (π:Equiv.Perm (Fin n)) (D:Fin n→Fin n→Prop)
      (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
      (ℓ:Fin K→ℕ),
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d mPath ℓ)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true
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
    ∀ (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
      (absorber:U→Finset (Fin n)) (δlocal:ℝ) (hU:0<Fintype.card U),
    P.IsRegularOfDegree Dv→(n:ℝ)/2≤Dv→ρ₀ ≤ initialIndexDensity U Dv→
    (∀x y,x≠y→(5/8:ℝ)*(1/100:ℝ)^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (y,w)=some (Sum.inr false))).card:ℝ))→
    (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>raw (Sum.inr e)) v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/(mPath:ℝ)+4*(n:ℝ)^(3/4:ℝ))→
    let H:=Q.extendedIndices 1
    let Kbad:=longRequiredPhysicalGraph P P₀ Sel π d I D M
    let Jbad:=spanningRestriction (P\Used) I\Kbad
    LongSelectedOrientedSourceWithLoad hU F P π d mPath ℓ raw t Jret σ H I Kbad absorber δlocal (matchSet.map q) →
    (∀c∈matchSet,∀c'∈matchSet,c≠c'→Disjoint
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) c)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) c'))→
    LongSelectedOrientedSourceWithLoadAndMatching hU F P π d mPath ℓ raw t Jret σ H I Kbad Used absorber δlocal
      (FirstVortexPrescribedAssignmentOutcome P Del Used Kbad I π d σ t Jret H α b ρ₀ θ ε lam) (matchSet.map q) :=by
  obtain ⟨N,hN⟩:=long_first_prescribed_matchings_from_event_and_aligned_old_packing α lam ε ρ₀ b θ eps ξ mPath d K hK hepsAssign hξ hα hlam hρ₀ hb hαb hbd hmPath hmarg hεsmall hd hd3
  refine ⟨N,?_⟩
  intro n hn U _ _ P Del Dv m β F hF hρhi Q π D σ ℓ R raw T S f q φ matchSet Used I P₀ Sel M u C₀ a γ δ hθ hθhi he hC hehi hlamhi hγ haD hγD hDel hδ hrow hmatch t Jret absorber δlocal hU hreg hDlo hρlo hpair hboundary H Kbad Jbad hsource hdisj
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  rcases hsource with ⟨Dsrc,orig,hPair,hValidCyc,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,PackOld,hOldDisj,hOldPack,hApprox,hSelected,hassign,hsize⟩
  have hValid:∀w p,p∈orig w→p.OriginalValid (Dsrc w):=by
    intro w p hp
    obtain ⟨a,xs,heq,hv⟩:=hValidCyc w p hp
    exact hv
  have hEdges:∀w,sourcePieceEdgesUnion (orig w)=(F w).edgeFinset:=fun w=>(hUnion w).2
  have hArc:∀w,ActualOldArcContainment (data w) (ψ w) (E w)
      (fun x y=>({x,y}:Finset (Fin n))∈longRawPhysicalHubRims P π d mPath ℓ raw true true (matchSet.map q) w):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,hh,_⟩
    exact hh
  let Old:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(mPath+1)*d) (inner w)).image (ψ w)
  have hOld:∀w,Disjoint (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w) (Old w):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,hh,_⟩
    exact hh.symm
  have hdec : instDecidableEqFin n = firstVortexAttachOrientedSourceFin n := Subsingleton.elim _ _
  have hdec6 : instDecidableEqFin 6 = firstVortexAttachOrientedSourceFin 6 := Subsingleton.elim _ _
  have hN' := hN n hn
  rw [hdec] at hN'
  try rw [hdec6] at hN'
  obtain ⟨Pack,hOldDisj',hOldPack',hApprox',hUsed,hMore⟩:=
    hN' U P Del Dv m β F hF hρhi Q π D σ true true ℓ matchSet C₀ a γ δ hθ hθhi he hC hehi hlamhi hγ haD hγD hDel hδ hrow hmatch _ _ _ F data E orig Dsrc hPair hValid hEdges hArcs hAlign ψ hdisj hArc
  have hSelected':∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→s(x,y)∉Pack:=
    selected_host_avoids_approximate_packing P π d σ Pack hApprox'
  have hExtra:=hMore t Jret Old hOld hreg hDlo hρlo hpair hboundary
  refine ⟨Dsrc,orig,hPair,hValidCyc,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,hOldDisj',hOldPack',hApprox',hSelected',hassign,hsize,hUsed,?_⟩
  dsimp only [] at hExtra
  dsimp only [FirstVortexPrescribedAssignmentOutcome, Kbad, Jbad, H, I, P₀, Sel, M, Used, raw, R, S, T, q, φ, Old]
  exact hExtra
end Oberwolfach
