module

public import Oberwolfach.ActualOrdinaryWheelImage
public import Oberwolfach.RawReservedSpokeList
public import Oberwolfach.ActualMatchedOldAvoidsList
public import Oberwolfach.MixedOutcomePackingBufferedWheelSupport
public import Oberwolfach.ActualMatchedOldRetainedAvoidance
public import Oberwolfach.MixedOutcomePackingBufferedEmbedding
public import Oberwolfach.LongRawAssignedWheelPacking
public import Oberwolfach.ActualMatchedPieceDirectedArcs
public import Oberwolfach.ActualMatchedPiecePhysicalEdges
public import Oberwolfach.LongRawHubWheelRimCoverage
public import Oberwolfach.ActualOldPhysicalCoverage

@[expose] public section
/-! Assemble the actual selected mixed matching, assigned ordinary cycles and
same-outcome interval labels into the buffered old-domain embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawMatchingAllWheelOccupancyFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_matching_buffered_embedding_with_all_wheel_occupancy
    {N K:ℕ} {U X Ksrc Jsrc I:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    [Fintype Ksrc] [DecidableEq Ksrc] [DecidableEq Jsrc] [Fintype I] [Nonempty (Fin N)]
    {F:SimpleGraph X} (data:ActualResidualData (K:=Ksrc) (J:=Jsrc) F)
    (P:SimpleGraph (Fin N)) (π:Equiv.Perm (Fin N)) (m:ℕ) (hc:data.c=m+1)
    (hnoshort:∀x l,0<l→l<2*data.d+1→(π^l) x≠x)
    (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin N) U Bool Bool) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π data.d (fun e=>raw (Sum.inr e)) false) t) (w:U)
    (index:Ksrc ≃ retainedAndRawIntervalIndex π data.d (fun e=>raw (Sum.inr e)) false true t Jret w):
    let state:=longRawHubState P π data.d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π data.d m ℓ
    let root:=fun i=>retainedAndRawIntervalRoot π data.d (fun e=>raw (Sum.inr e)) false true t Jret w (index i)
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'))→
    ∀(select:{j // j∈data.t}↪LongRawSelectedOrdinary π data.d m ℓ e M),
    (∀j,ℓ (longRawSelectedOrdinaryPayload π data.d m ℓ e M (select j)).1=(data.C j.val).length)→
    (∀j,(longRawSelectedOrdinaryWheel π data.d m ℓ e M (select j)).val.2=w)→
    let S:=longRawMarkedWheelsAtHub P π data.d m ℓ raw true true M w
    (∀i∈data.s₂,data.T i=packedPhysicalSpokePositions _ _ _ _ m (3*data.d) data.d π
      (rawMarkedPairSpokes π data.d raw true true false) (rawMarkedPairSpokes π data.d raw true true true) S w (root i))→
    F.IsRegularOfDegree 2→(data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)→
    ∀(ext:∀i:Ksrc,Fin (data.c*data.d+5)↪X),
    (∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))→
    (∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))→
    ∀(bidx:I≃{i // i∈data.s₁}) (finalExt:∀i:I,Fin (data.c*data.d+5)↪X)
      (inner:∀i:I,Fin (data.c*data.d+1)↪X),
    (∀i p,inner i p=finalExt i ⟨p.val+2,by omega⟩)→
    (∀i,(data.P (bidx i).val).support=List.ofFn (finalExt i))→
    (∀i p,inner i p=ext (bidx i).val ⟨p.val+2,by omega⟩)→
    (∀i:Ksrc,i∈data.s₁∨i∈data.s₂)→
    (∀i∈data.s₂,∃a:{a:Fin N // rawIntervalColouredStart π data.d (fun e=>raw (Sum.inr (w,e))) a true},index i=Sum.inr a)→
    ∃ψ:X→Fin N,
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X) ∧
      (∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
        ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root i)) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (root r.1.val)) ∧
      (∀j∈data.t,∀k<(data.C j).length,rawMixedPhysicalArc P π data.d raw
        (ψ ((data.C j).getVert k)) (ψ ((data.C j).getVert (k+1)))) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,rawMixedPhysicalArc P π data.d raw
        (ψ ((data.path (.inr r)).getVert k)) (ψ ((data.path (.inr r)).getVert (k+1)))) ∧
      ActualOldPhysicalCoverage data ψ (longRawPhysicalHubRims P π data.d m ℓ raw true true M w) ∧
      (∀x,x∈data.oldDomain→x∉bufferedPathFullDomain (fun _=>data.c*data.d) inner→
        ψ x∉markedIntervalRootSet π (fun _:retainedMarkedIndex π data.d (fun e=>raw (Sum.inr e)) false t Jret w=>data.d) Subtype.val) ∧
      Disjoint ((data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ)
        (rawReservedSpokeList π data.d (fun e=>raw (Sum.inr e)) w) ∧
      (∀j:{j // j∈data.t},∀x∈Finset.univ.image ((longRawSelectedOrdinaryWheel π data.d m ℓ e M (select j)).val.1.val),
        x∈(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ) ∧
      ∃W:actualSelectedSegmentIndex data→{W // W∈S},
      (∀z,(W z).val.1.val 0=(π^z.2.val.val) (root z.1.1.val)) ∧
      (∀z:actualSelectedSegmentIndex data,∀i:Fin (m+1),(W z).val.1.val i∈(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ):=by
  intro state e R root M hmatch select hlen hhub S hT hF hCycle ext hsupp hsrc bidx finalExt inner hinner hfinal hinnerExt hactive happrox
  let n (j:{j // j∈data.t}):ℕ:=(data.C j.val).length-1
  have hlenSource:∀j,(data.C j.val).length=n j+1:=by
    intro j
    have hh:3≤(data.C j.val).length:=(data.hcycle j.val j.property).isCircuit.three_le_length
    dsimp [n];omega
  have hn:∀j,2≤n j:=by
    intro j
    have hh:3≤(data.C j.val).length:=(data.hcycle j.val j.property).isCircuit.three_le_length
    dsimp [n];omega
  have hlen':∀j,ℓ (longRawSelectedOrdinaryPayload π data.d m ℓ e M (select j)).1=n j+1:=by
    intro j
    exact (hlen j).trans (hlenSource j)
  let r:=fun a:LongRawSelectedOrdinary π data.d m ℓ e M=>ℓ (longRawSelectedOrdinaryPayload π data.d m ℓ e M a).1
  let Q:=fun a:LongRawSelectedOrdinary π data.d m ℓ e M=>(longRawSelectedOrdinaryWheel π data.d m ℓ e M a).val
  let C:=reindexedOrdinaryWheel π (3*data.d) r Q n select hlen'
  have hp:=long_raw_matching_gives_hub_packing P π data.d m ℓ raw true true M hmatch w
  have ha:=long_raw_assigned_wheel_packing P π data.d m ℓ raw true true M hmatch w n select hlen' hhub
  have hraw:=raw_mixed_sampled_arcs_in_physical_host P π data.d raw
  have hb:1≤3*data.d:=by have hh:=data.hd;omega
  obtain ⟨W,u,v,q,g,f,ψ,hW,hq,hqLen,hqDis,hcy,hrun,hg,hf,hψ,hψf,hψg,hparent,htarget,hclose,hcedges,hdir,hedges,hWheelSupport⟩:=
    mixed_outcome_physical_packing_buffered_embedding_with_wheel_support data P _ _ _ _ m (3*data.d) hc π hb hnoshort raw false true (by decide) true t Jret w index
      S hp.1 hp.2.1 hT n hn C hlenSource ha.1 ha.2.1 ha.2.2.2.1 ha.2.2.2.2 hraw.1 hraw.2.1
      (rawMixedPhysicalArc P π data.d raw) hraw.2.2.1 hraw.2.2.2.1 ha.2.2.1 hF hCycle ext hsupp hsrc bidx finalExt inner hinner hfinal
  have ⟨hpieces,hfirst⟩:=actual_matched_piece_directed_arcs data (SimpleGraph.completeGraph (Fin N)) u v q hqLen
    (rawMixedPhysicalArc P π data.d raw) hdir hclose ψ f hψf hf
  have hcycleArcs:=actual_matched_cycle_directed_arcs data ψ (rawMixedPhysicalArc P π data.d raw) hpieces hfirst
  have hrunArcs:∀r:SelectedRunIndex data.s₂ data.d data.T,∀k<(data.path (.inr r)).length,
      rawMixedPhysicalArc P π data.d raw (ψ ((data.path (.inr r)).getVert k)) (ψ ((data.path (.inr r)).getVert (k+1))):=by
    intro r k hk
    exact hpieces (.inr r) k hk
  let Pack:=longRawPhysicalHubRims P π data.d m ℓ raw true true M w
  have hWp:∀z,markedCyclePhysicalEdges _ _ _ _ m π (3*data.d) (W z).1⊆Pack:=by
    intro z
    exact long_raw_hub_marked_rims_covered P π data.d m ℓ raw true true M w (W z) (hW z).1
  have hQ:∀j (i:Fin (r (select j))),{(Q (select j)).1.val i,(Q (select j)).1.val (cycleNext i)}∈Pack:=by
    intro j i
    have hh:=(long_raw_selected_wheel_rims_covered P π data.d m ℓ raw true true M).2 (select j) i
    dsimp only [Q,Pack] at *
    rw [hhub j] at hh
    exact hh
  have hCp:∀j a,{(C j).1.val a,(C j).1.val (cycleNext a)}∈Pack:=
    reindexed_ordinary_rim_covered π (3*data.d) r Q n select hlen' Pack hQ
  have ⟨hpiecesPhysical,hcyclePhysical⟩:=actual_matched_piece_physical_edges_from_wheels data _ _ _ _ m (3*data.d) π _ _ W n C u v q hqLen htarget hcedges hedges Pack hCp hWp ψ f hψf hf
  have hphysical:ActualOldPhysicalCoverage data ψ Pack:=by
    refine ⟨hcyclePhysical,?_⟩
    intro r k hk
    exact hpiecesPhysical (.inr r) k hk
  have hpres:∀i (j:Fin (data.d+1)),bufferedMarker data.c data.d (ext i) j∈data.prescribed→
      ψ (bufferedMarker data.c data.d (ext i) j)=(π^j.val) (root i):=by
    intro i j hj
    rw [hψg _ hj]
    exact hg i j hj
  have hOldAvoid:=actual_matched_old_avoids_retained_roots hF data hCycle ext hsupp bidx inner hinnerExt hactive π hnoshort
    (fun e=>raw (Sum.inr e)) t Jret w index happrox (SimpleGraph.completeGraph (Fin N)) u v q hcy hrun ψ hpres f hψf hf
  let L:=rawReservedSpokeList π data.d (fun e=>raw (Sum.inr e)) w
  let Ord:=rawIntervalOrdinaryOuter π data.d (fun e=>raw (Sum.inr e)) true w
  have hL:=raw_reserved_spoke_list_avoids_old_labels π data.d
    (fun e=>raw (Sum.inr e)) t Jret w
  have hlabels:∀i (j:Fin (data.d+1)),(π^j.val) (root i)∉L:=fun i j=>hL.2 (index i) j
  have hOldList:=actual_matched_old_image_avoids_list hF data hCycle ext hsupp bidx inner hinnerExt π root Ord L
    (SimpleGraph.completeGraph (Fin N)) u v q hcy hrun hL.1.symm hlabels ψ hpres f hψf hf
  let rim:∀j:{j // j∈data.t},Fin (n j+1)↪Fin N:=fun j=>⟨(C j).1.val,permutationSeparated_injective π (3*data.d) (C j).1.val (C j).1.property⟩
  have hend:∀j,∃k:Fin (n j+1),v (.inl j)=rim j k:=by
    intro j
    exact ⟨0,(htarget j).2⟩
  have hinside:∀j k,k<(q (.inl j)).length→∃a:Fin (n j+1),(q (.inl j)).getVert k=rim j a:=by
    intro j k hk
    obtain ⟨a,ha,_⟩:=hcedges j k hk
    exact ⟨a,ha⟩
  have hOcc:=actual_ordinary_wheel_rim_in_old_image data hF hCycle u v q hq hqLen f ψ hψf hf n rim hlenSource hend hinside
  have hInteriors:=actual_final_interiors_eq_buffered_strict data bidx finalExt inner hinner hfinal
  rw [hInteriors] at hOcc
  have hRim:∀j:{j // j∈data.t},∀x∈Finset.univ.image ((longRawSelectedOrdinaryWheel π data.d m ℓ e M (select j)).val.1.val),
      x∈(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ:=by
    intro j x hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    let k':Fin (n j+1):=Fin.cast (hlen' j) k
    have hh:=hOcc j k'
    have heq:(rim j k')=(longRawSelectedOrdinaryWheel π data.d m ℓ e M (select j)).val.1.val k:=by
      change (C j).1.val k'=(Q (select j)).1.val k
      have hk:=cast_ordinary_wheel_vertex (hlen' j) (Q (select j)) k'
      change (C j).1.val k'=(Q (select j)).1.val (Fin.cast (hlen' j).symm k') at hk
      simpa only [k',Fin.cast_cast,Fin.cast_refl,id_eq] using hk
    simpa only [heq] using hh
  have hTarget:=actual_old_piece_target_support_in_old_image data hF hCycle u v q hq hqLen f ψ hψf hf
  rw [hInteriors] at hTarget
  let W':actualSelectedSegmentIndex data→{W // W∈S}:=fun z=>⟨W z,(hW z).1⟩
  have hWRoot:∀z,(W' z).val.1.val 0=(π^z.2.val.val) (root z.1.1.val):=fun z=>(hW z).2.2
  have hWImage:∀z:actualSelectedSegmentIndex data,∀i:Fin (m+1),(W' z).val.1.val i∈(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner).image ψ:=by
    intro z i
    exact hTarget (.inr z.1) (List.mem_toFinset.mpr (hWheelSupport z i))
  exact ⟨ψ,hψ,hpres,hparent,hcycleArcs,hrunArcs,hphysical,hOldAvoid,hOldList,hRim,W',hWRoot,hWImage⟩
end Oberwolfach
