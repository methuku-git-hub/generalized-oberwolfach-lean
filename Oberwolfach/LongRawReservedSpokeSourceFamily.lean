module

public import Oberwolfach.ActualSumBufferedInteriorsDeleted
public import Oberwolfach.LongRawSourceEmbeddingReservedSpokes
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
local instance longRawReservedSpokeFamilyDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_reserved_spoke_source_family_and_old_packing
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
      Disjoint (bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)) (data w).remaining ∧
      Set.InjOn (ψ w) (↑((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)):Set (Fin N)) ∧
      ActualOldArcContainment (data w) (ψ w) (E w)
        (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ∧
      Disjoint (((data w).oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) (inner w)).image (ψ w))
        (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w)) ∧
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    ∃Pack:Finset (Sym2 (Fin N)),
      (∀w z,w≠z→Disjoint (old w) (old z)) ∧ (∀w,old w⊆Pack):=by
  intro ℓ state e R M hmatch hmaps
  obtain ⟨assign,hhub,hsize,hSource⟩:=long_raw_source_embeddings_from_matching_and_starts_with_reserved_spokes F hF E Allowed hAllowed hn hK hclass P₀ π d m hd hm hnoshort θ hθ hcut hlarge raw t Jret hcounts M hmatch hmaps
  have hex:∀w,∃(data:ActualResidualData
      (K:=(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w) ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})
      (J:={a:LongRawSelectedOrdinary π d m ℓ e M // (assign a).1=w}) (F w))
      (ext:(retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w ⊕
        {a:Fin N // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) a true})→Fin ((m+1)*d+5)↪Fin N)
      (inner:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w→Fin ((m+1)*d+1)↪Fin N)
      (ψ:Fin N→Fin N),
      data.c=m+1 ∧ data.d=d ∧ data.s₁=firstSumIndices ∧
      data.Cembed=data.t.biUnion (fun j=>(data.C j).support.toFinset) ∧
      (∀i,(data.P i).support=List.ofFn (ext i)) ∧
      (∀a k,inner a k=ext (.inl a) ⟨k.val+2,by omega⟩) ∧
      (∀i (j:Fin (d+1)),bufferedMarker (m+1) d (ext i) j∈data.prescribed→
        ψ (bufferedMarker (m+1) d (ext i) j)=(π^j.val)
          (retainedAndRawIntervalRoot π d (fun e=>raw (Sum.inr e)) false true t Jret w i)) ∧
      Disjoint (bufferedPathStrictInterior (fun _=>(m+1)*d) inner) data.remaining ∧
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner):Set (Fin N)) ∧
      ActualOldArcContainment data ψ (E w)
        (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w) ∧
      Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>(m+1)*d) inner).image ψ)
        (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w):=by
    intro w
    obtain ⟨block,data,ext,inner,ψ,hdata⟩:=hSource w
    rcases hdata with ⟨hc,hd',hs1,hs2,ht,hC,hT,hSupp,hExt,hdis,hInner,hCycle,hOrient,hInj,hMarker,hInS,hDirected,hArc,hCoverage,hRim,hAvoidRoot,hList⟩
    have hDR:=actual_sum_buffered_interiors_deleted_with_parameters data (m+1) d hc hd' hs1 ext inner hSupp hInner
    exact ⟨data,ext,inner,ψ,hc,hd',hs1,hC,hSupp,hInner,hMarker,hDR,hInj,hRim,hList⟩
  choose data ext inner ψ hprops using hex
  have hold:∀w,ActualOldArcContainment (data w) (ψ w) (E w)
        (fun x y=>({x,y}:Finset (Fin N))∈longRawPhysicalHubRims P₀ π d m ℓ raw true true M w):=fun w=>(hprops w).2.2.2.2.2.2.2.2.2.1
  obtain ⟨Pack,hdis,hsub⟩:=long_raw_matching_actual_old_packing P₀ π d m ℓ raw true true F data E pieces Dsrc hpair hvalid hEdges hArcs halign ψ M hmatch hold
  exact ⟨assign,data,ext,inner,ψ,hprops,Pack,hdis,hsub⟩
end Oberwolfach
