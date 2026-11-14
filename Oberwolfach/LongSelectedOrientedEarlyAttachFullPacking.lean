module

public import Oberwolfach.LongSelectedExactOrientedSourceWithLoad
public import Oberwolfach.LongSelectedOrientedSourceWithLoad
public import Oberwolfach.LongSelectedOrientedSourceExactOld
public import Oberwolfach.LongRawSurvivingExactOldPacking
public import Oberwolfach.SelectedHostAvoidsApproximatePacking

@[expose] public section
/-! The actual old packing and any assignment valid for it can be attached
to the aligned residual source of the same surviving matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance selectedOrientedEarlyAttachFullPackingFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem long_selected_oriented_early_source_attach_full_packing_assignment
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hU:0<Fintype.card U) (F:U→SimpleGraph (Fin n)) (P Del:SimpleGraph (Fin n))
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σ (Sum.inr e))) false) t)
    (H:Finset U) (A:Finset (Fin n)) (Kbad:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ)
    (Extra:(U→Finset (Fin n))→Finset (Sym2 (Fin n))→Prop):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q);
    LongSelectedExactOrientedSourceWithLoad hU F P π d m ℓ raw t Jret σ H A Kbad absorber δ (M.map q)→
    (∀c∈M,∀c'∈M,c≠c'→Disjoint
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) c)
      (restrictedResourceSet R (Function.Embedding.subtype (·∈S)) c'))→
    (∀Old Pack,(∀w,Disjoint (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w) (Old w))→
      Pack⊆Used.edgeFinset→Extra Old Pack)→
    LongSelectedOrientedSourceExactOld hU F P π d m ℓ raw t Jret σ H A Kbad Used absorber δ (fun Old Pack=>Extra Old Pack ∧ Pack=Used.edgeFinset) (M.map q):=by
  intro R raw T S q φ M Used hsource hdisj hassign
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  unfold LongSelectedOrientedSourceExactOld
  have htarget:selectedOrientedSourceExactOldFin n=selectedOrientedEarlyAttachFullPackingFin n:=Subsingleton.elim _ _
  have htargetK:selectedOrientedSourceExactOldFin K=selectedOrientedEarlyAttachFullPackingFin K:=Subsingleton.elim _ _
  try rw [htarget]
  try rw [htargetK]
  rcases hsource with ⟨Dsrc,orig,hPair,hValidCyc,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,PackOld,hOldDisj,hOldPack,hApprox,hSelected,hExactOld,hEqOld,hassignOld,hsize⟩
  have hValid:∀w p,p∈orig w→p.OriginalValid (Dsrc w):=by
    intro w p hp
    obtain ⟨a,xs,heq,hv⟩:=hValidCyc w p hp
    exact hv
  have hEdges:∀w,sourcePieceEdgesUnion (orig w)=(F w).edgeFinset:=fun w=>(hUnion w).2
  have hArc:∀w,ActualOldArcContainment (data w) (ψ w) (E w)
      (fun x y=>({x,y}:Finset (Fin n))∈longRawPhysicalHubRims P π d m ℓ raw true true (M.map q) w):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,hh,_⟩
    exact hh
  let Old:=fun w=>((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)
  have hOld:∀w,Disjoint (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w) (Old w):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,hh,_⟩
    exact hh.symm
  have hdec : instDecidableEqFin n = longRawSurvivingOldPackingCoveredDecEqFin n := Subsingleton.elim _ _
  have hdisj' := hdisj
  have hArc' := hArc
  try rw [hdec] at hdisj'
  try rw [hdec] at hArc'
  let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
    (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
  let Pack:=Finset.univ.biUnion old
  obtain ⟨hOldDisj',hOldPack',hApprox',hUsed⟩:=
    long_raw_surviving_matching_exact_old_packing_in_covered_graph P π d m ℓ σ true true Del.edgeFinset F data E orig Dsrc
      hPair hValid hEdges hArcs hAlign ψ M hdisj' hArc'
  try rw [←hdec] at hOldDisj'
  try rw [←hdec] at hOldPack'
  try rw [←hdec] at hApprox'
  try rw [←hdec] at hUsed
  have hlocal:instDecidableEqFin n=selectedOrientedEarlyAttachFullPackingFin n:=Subsingleton.elim _ _
  try rw [hlocal] at hOldDisj'
  try rw [hlocal] at hOldPack'
  try rw [hlocal] at hApprox'
  try rw [hlocal] at hUsed
  have hUsed':Pack⊆Used.edgeFinset:=by
    simpa only [Used,R,raw,T,S,q,φ] using hUsed
  have hSelected':∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→s(x,y)∉Pack:=
    selected_host_avoids_approximate_packing P π d σ Pack hApprox'
  refine ⟨Dsrc,orig,hPair,hValidCyc,hUnion,hArcs,E,hAlign,hLate,ext,inner,ψ,assign,data,hprops,hload,pieces,hpieceEdge,hpieceArc,Pack,rfl,hOldDisj',hOldPack',hApprox',hSelected',hassignOld,hsize,hUsed',?_⟩
  constructor
  · exact hassign Old Pack hOld hUsed'
  · have hh:PackOld=Used.edgeFinset:=by
      simpa only [Used,R,raw,T,S,q,φ] using hEqOld
    exact hExactOld.symm.trans hh
end Oberwolfach
