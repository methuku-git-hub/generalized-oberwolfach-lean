module

public import Oberwolfach.LongRawAlignedPackingOriented
public import Oberwolfach.LongRawAlignedPackingProtection
public import Oberwolfach.LongRawAlignedAllWheelOccupancySelectedHost
public import Oberwolfach.LongRawSurvivingMatchingLift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawSurvivingAlignedOrientedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_surviving_aligned_source_with_oriented_protection
    {N K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin N)]
    (F:U→SimpleGraph (Fin N)) (hF:∀w,(F w).IsRegularOfDegree 2) (hU:0<Fintype.card U)
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
    (Del:Finset (Sym2 (Fin N)))
    : letI:Nonempty U:=Fintype.card_pos_iff.mp hU
      ∃(Dsrc:∀w,Fin N→Fin N→Prop) (orig:∀w,List (PrescribedSourcePiece (Fin N))),
      (∀w,(orig w).Pairwise (fun p q=>Disjoint p.vertices.toFinset q.vertices.toFinset)) ∧
      (∀w p,p∈orig w→∃a xs,p=.cycle a xs ∧ p.OriginalValid (Dsrc w)) ∧
      (∀w,sourcePieceVerticesUnion (orig w)=Finset.univ ∧ sourcePieceEdgesUnion (orig w)=(F w).edgeFinset) ∧
      (∀w x y,Dsrc w x y↔(x,y)∈sourcePieceArcsUnion (orig w)) ∧
      ∃E:∀w (C:(F w).ConnectedComponent),SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
        (∀w x,Dsrc w x (factorCycleOrientation (F w) (E w) x)) ∧
        LateComplementContinuation (V:=Fin N) F Dsrc ∧
    let ℓ:=longAssignedPaddedLength (K:=K)
    let state:=longRawHubState P₀ π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P₀ π d raw true true Del
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T (long_raw_surviving_resources_subset P₀ π d raw true true Del)
    let eS:{z // z∈S}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) eS),
    (∀x∈M,∀y∈M,x≠y→Disjoint (restrictedResourceSet (mixedCandidateResources R) eS x)
      (restrictedResourceSet (mixedCandidateResources R) eS y))→
    let Lifted:=M.map q
    LongRawOrdinaryComponentMapsProperty F π d m ℓ e Lifted→
    ∃assign:LongRawSelectedOrdinary π d m ℓ e Lifted↪(Σw,(F w).ConnectedComponent),
    ∃(data:∀w,ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ e Lifted // (assign a).1=w}) (F w))
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
        (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true Lifted w) ∧
      Disjoint (((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w))
        (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w) ∧
      (data w).s₂=secondSumIndices ∧ (data w).t=Finset.univ ∧
      (∀i,(data w).T i=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
        (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true)
        (longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true Lifted w) w
        (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      (∀j,((data w).C j).length=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Lifted j.val).1) ∧
      (∀j,((data w).C j).toSubgraph.verts=
        (assignedComponentAtHub F (fun a=>(assign a).1) (fun a=>(assign a).2) w j).supp) ∧
      (∀j:{a:LongRawSelectedOrdinary π d m ℓ e Lifted // (assign a).1=w},∀x∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ e Lifted j.val).val.1.val),
        x∈((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) ∧
      (∀W∈longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true Lifted w,∀i:Fin (m+1),
        W.1.val i∈((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w)) ∧
      (∀i j,i≠j→Disjoint (Finset.univ.image (ext w i)) (Finset.univ.image (ext w j))) ∧
      (∀x,x∈(data w).oldDomain→x∉bufferedPathFullDomain (fun _=>(m+1)*d) (inner w)→
        ψ w x∉markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w=>d) Subtype.val) ∧
      (∀i (j:Fin ((m+1)*d+4)),factorCycleOrientation (F w) (E w) (ext w i j.castSucc)=ext w i j.succ) ∧
      ActualOldArcContainment (data w) (ψ w) (E w) (rawMixedPhysicalArc P₀ π d raw)) ∧
    ∃(pieces:∀w,List (PrescribedSourcePiece {x // x∈(data w).remaining})),
      (∀w,prescribedDependentGraph pieces w=((data w).graph).induce (↑(data w).remaining:Set (Fin N))) ∧
      (∀w x y,prescribedDependentDigraph pieces w x y ↔ Dsrc w x.1 y.1 ∧ (data w).graph.Adj x.1 y.1) ∧
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin N)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack) ∧
      Pack⊆(longApproximatePhysicalGraph P₀ π d σ).edgeFinset ∧
      (∀x y,rawSelectedPhysicalRelation P₀ π d (fun e=>σ (Sum.inl e)) x y→s(x,y)∉Pack) ∧
      (∀a,(assign a).1=(longRawSelectedOrdinaryWheel π d m ℓ e Lifted a).val.2) ∧
      (∀a,Fintype.card (assign a).2=ℓ (longRawSelectedOrdinaryPayload π d m ℓ e Lifted a).1) :=by
  letI:Nonempty U:=Fintype.card_pos_iff.mp hU
  obtain ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,hfamily⟩:=
    long_raw_aligned_covered_packing_with_oriented_protection F hF hU Allowed hAllowed hn hK hclass P₀ π d m hd hm hnoshort θ hθ hcut hlarge raw t Jret hcounts σ hraw
  refine ⟨Dsrc,orig,hpair,hcycles,hwhole,hArcs,E,halign,hres,?_⟩
  intro ℓ state e R T S q eS M hmatch Lifted hmaps
  have hdec : longRawSurvivingAlignedOrientedFin N = instDecidableEqFin N := Subsingleton.elim _ _
  have hmatch' := hmatch
  rw [hdec] at hmatch'
  have hlift := (long_raw_surviving_matching_lift P₀ π d m ℓ raw true true Del M hmatch').1
  rw [← hdec] at hlift
  obtain ⟨assign,data,ext,inner,ψ,hprops,pieces,hgraph,harcs,Pack,hdis,hsub,hLayer,hUsed,hAvoid,hhub,hsize⟩:=hfamily Lifted hlift hmaps
  exact ⟨assign,data,ext,inner,ψ,hprops,pieces,hgraph,harcs,Pack,hdis,hsub,hLayer,hAvoid,hhub,hsize⟩
end Oberwolfach
