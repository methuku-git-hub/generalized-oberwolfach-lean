module

public import Oberwolfach.LongRawSourceFamilyAllRimEdges
public import Oberwolfach.LongRawAllRimsExactOld
public import Oberwolfach.LongRawActualOldPackingCovered
public import Oberwolfach.LongRawMatchingOldPackingAvoidsSelectedHost
public import Oberwolfach.ActualSumBufferedInteriorsDeleted
public import Oberwolfach.LongRawSourceEmbeddingFromEventProtectedList
public import Oberwolfach.LongRawMatchingActualOldPacking
public import Oberwolfach.LongRawComponentAssignmentFromMaps
public import Oberwolfach.LongAssignedActualIntervalCapacityDecidable
public import Oberwolfach.LongAssignedPaddedLengths

@[expose] public section
/-! Actual long source paths and their old embeddings from one matching,
the original class hypothesis, and the same-outcome hub start counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawComponentAllRimsExactHostFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_component_all_rims_exact_selected_host_packing
    {N K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin N)]
    (F:U→SimpleGraph (Fin N)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (E:∀w (D:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card D) ≃g D.toSimpleGraph)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (hn:0<N) (hK:3≤K) (hclass:∀w,factorPreparationClass (F w) K=none)
    (P₀:SimpleGraph (Fin N)) (π:Equiv.Perm (Fin N)) (d m:ℕ) (hd:2≤d) (hm:7≤m)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (θ:ℝ) (hθ:0<θ)
    (hcut:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K+1)≤θ/2)
    (hlarge:8*((m:ℝ)+1)/θ<(N:ℝ)^((1:ℝ)/4))
    (raw:RawMarkedOutcome (Fin N) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (hcounts:∀w g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (N:ℝ)*longAssignedIntervalProbability F hF K m θ w g/d|<(N:ℝ)^(3/4:ℝ)/d)
    (σ:∀e:RawWheelCoordinate (Fin N) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (hraw:raw=(fun e=>rawExpandedApproximateCollapse e (σ e)))
    (pieces:∀w,List (PrescribedSourcePiece (Fin N))) (Dsrc:∀w,Fin N→Fin N→Prop)
    (hpair:∀w,(pieces w).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset))
    (hvalid:∀w p,p∈pieces w→p.OriginalValid (Dsrc w))
    (hEdges:∀w,sourcePieceEdgesUnion (pieces w)=(F w).edgeFinset)
    (hArcs:∀w x y,Dsrc w x y↔(x,y)∈sourcePieceArcsUnion (pieces w))
    (halign:∀w x,Dsrc w x (factorCycleOrientation (F w) (E w) x)):
    let ℓ:=longAssignedPaddedLength (K:=K)
    let state:=longRawHubState P₀ π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀x∈M,∀y∈M,x≠y→Disjoint (restrictedResourceSet (mixedCandidateResources R) e x)
      (restrictedResourceSet (mixedCandidateResources R) e y))→
    LongRawOrdinaryComponentMapsProperty F π d m ℓ e M→
    ∃assign:LongRawSelectedOrdinary π d m ℓ e M↪(Σw,(F w).ConnectedComponent),
    ∃(data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}) (F w))
      (ext:∀w,(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})→Fin ((m+1)*d+5)↪Fin N)
      (inner:∀w,retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w→Fin ((m+1)*d+1)↪Fin N)
      (ψ:∀w,Fin N→Fin N),
    (∀w,(data w).c=m+1 ∧ (data w).d=d ∧ (data w).s₁=firstSumIndices ∧
      (data w).Cembed=(data w).t.biUnion (fun j=>((data w).C j).support.toFinset) ∧
      (∀i,((data w).P i).support=List.ofFn (ext w i)) ∧
      (∀a k,inner w a k=ext w (.inl a) ⟨k.val+2,by omega⟩) ∧
      (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext w i) j∈(data w).prescribed→
        ψ w (bufferedMarker (m+1) d (ext w i) j)=(π^j.val)
          (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀i∈(data w).s₂,∀j:Fin (d+1),∃x∈(data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w),
        ψ w x=(π^j.val) (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      Disjoint (bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)) (data w).remaining ∧
      Set.InjOn (ψ w) (↑((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)):Set (Fin N)) ∧
      ActualOldArcContainment (data w) (ψ w) (E w)
        (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ∧
      Disjoint (((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w))
        (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w) ∧
      (data w).s₂=secondSumIndices ∧ (data w).t=Finset.univ ∧
      (∀i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true M w) w
        (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀j,((data w).C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M j.val).1) ∧
      (∀j,((data w).C j).toSubgraph.verts=
        (assignedComponentAtHub F (fun a=>(assign a).1) (fun a=>(assign a).2) w j).supp) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w},∀x∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ e M j.val).val.1.val),
        x∈((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) ∧
      (∀W∈longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true M w,∀i:Fin (m+1),
        W.1.val i∈((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) ∧
      ActualWheelRimsFamilyOld (data w) (ψ w) _ _ _ _ m (3*d) π _ _ (longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true M w) ∧
      ActualAssignedOrdinaryRimsOld (data w) (ψ w)
        (fun j:{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}=>ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M j.val).1)
        (fun j=> (longRawSelectedOrdinaryWheel π d m ℓ e M j.val).val.1.val)) ∧
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin N)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack) ∧
      Pack⊆(longApproximatePhysicalGraph P₀ π d σ).edgeFinset ∧
      (∀x y,rawSelectedPhysicalRelation P₀ π d (fun e=>σ (Sum.inl e)) x y→s(x,y)∉Pack) ∧
      Pack=Finset.univ.biUnion old ∧
      Pack=(physicalRimCandidateUnion (markedRawSampledPhysicalEmbedding P₀ π d raw true true)
        (restrictedResourceSet (mixedCandidateResources R) e) M).edgeFinset ∧
      (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2) ∧
      (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1):=by
  subst raw
  intro ℓ state e R M hmatch hmaps
  obtain ⟨assign,data,ext,inner,ψ,hprops,_,_,_,hhub,hsize⟩:=
    long_raw_reserved_spoke_source_family_with_all_rim_edges F hF E Allowed hAllowed hn hK hclass P₀ π d m hd hm hnoshort θ hθ hcut hlarge (fun e=>rawExpandedApproximateCollapse e (σ e)) t Jret hcounts pieces Dsrc hpair hvalid hEdges hArcs halign M hmatch hmaps
  have hold:∀w,ActualOldArcContainment (data w) (ψ w) (E w)
    (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ
      (fun e=>rawExpandedApproximateCollapse e (σ e)) true true M w):=fun w=>(hprops w).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨Pack,hdis,hsub,hLayer,hAvoid⟩:=
    long_raw_matching_actual_old_packing_avoids_selected_host P₀ π d m ℓ σ true true F data E pieces Dsrc hpair hvalid hEdges hArcs halign ψ M hmatch hold
  obtain ⟨Alloc,_,hsubAlloc,_,hAllocUsed⟩:=
    long_raw_matching_actual_old_packing_in_covered_graph P₀ π d m ℓ σ true true F data E pieces Dsrc hpair hvalid hEdges hArcs halign ψ M hmatch hold
  let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
    (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
  let Exact:=Finset.univ.biUnion old
  have hExactPack:Exact⊆Pack:=by
    intro a ha
    obtain ⟨w,_,hw⟩:=Finset.mem_biUnion.mp ha
    exact hsub w hw
  have hExactAlloc:Exact⊆Alloc:=by
    intro a ha
    obtain ⟨w,_,hw⟩:=Finset.mem_biUnion.mp ha
    exact hsubAlloc w hw
  have hMarked:∀w,ActualWheelRimsFamilyOld (data w) (ψ w) _ _ _ _ m (3*d) π _ _
      (longRawMarkedWheelsAtHub P₀ π d m ℓ (fun e=>rawExpandedApproximateCollapse e (σ e)) true true M w):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_⟩
    exact hh
  have hOrd:∀w,ActualAssignedOrdinaryRimsOld (data w) (ψ w)
      (fun j:{a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}=>ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M j.val).1)
      (fun j=>(longRawSelectedOrdinaryWheel π d m ℓ e M j.val).val.1.val):=by
    intro w
    rcases hprops w with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh⟩
    exact hh
  have heq:=long_raw_all_rims_exact_old P₀ π d m ℓ (fun e=>rawExpandedApproximateCollapse e (σ e)) true true F data ψ M (fun a=>(assign a).1) hMarked hOrd (hExactAlloc.trans hAllocUsed)
  refine ⟨assign,data,ext,inner,ψ,hprops,Exact,hdis,?_,hExactPack.trans hLayer,?_,rfl,heq,hhub,hsize⟩
  · intro w a ha
    exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,ha⟩
  · intro x y hsel hmem
    exact hAvoid x y hsel (hExactPack hmem)
end Oberwolfach
