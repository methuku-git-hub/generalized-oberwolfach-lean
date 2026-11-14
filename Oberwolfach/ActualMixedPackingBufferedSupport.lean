module

public import Oberwolfach.ActualMixedPackingTargetPieces
public import Oberwolfach.ActualMatchedEmbeddingWithoutCrossHypothesis

@[expose] public section
/-! Assemble the physical mixed packing and the prescribed anchors into one
injection on the actual buffered complement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 32000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_mixed_packing_buffered_embedding_with_support
    {X V U E L K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [DecidableEq K] [DecidableEq J] [Fintype K] [Fintype I] [Nonempty V]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (hc:data.c=m+1)
    (π:Equiv.Perm V) (hb:1≤b) (hπ:∀x,π x≠x) (H₀ Hₖ:V→U→Prop) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U)
    (hpack:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hT:∀i∈data.s₂,data.T i=packedMarkedPositions tail head ktail khead m b data.d π H₀ Hₖ M hub (root i))
    (Ord:Finset V) (hOrd:∀W∈M,∀a:Fin (m+1),a.val≠0→W.1.val a∈Ord)
    (havoid:∀i,Disjoint (permutationWindow π 0 data.d (root i)) Ord)
    (n:{j // j∈data.t}→ℕ) (hn:∀j,2≤n j)
    (C:∀j:{j // j∈data.t},OrderedOrdinaryWheel (U:=U) π b (n j+1))
    (hlenC:∀j,(data.C j.val).length=n j+1) (hhubC:∀j,(C j).2=hub)
    (hOrdC:∀j a,(C j).1.val a∈Ord)
    (hCC:∀j k,j≠k→Disjoint (ordinaryWheelPhysicalResources (C j)) (ordinaryWheelPhysicalResources (C k)))
    (hCM:∀j W,W∈M→Disjoint (ordinaryWheelPhysicalResources (C j)) (markedWheelPhysicalResources W))
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:L,G.Adj (ktail e) (π (khead e)))
    (R:V→V→Prop) (hER:∀e:E,R (tail e) (head e)) (hKR:∀e:L,R (ktail e) (π (khead e)))
    (hCR:∀j a,R ((C j).1.val a) ((C j).1.val (cycleNext a)))
    (hG:F.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (index:I≃{i // i∈data.s₁}) (finalExt:∀i:I,Fin (data.c*data.d+5)↪X)
    (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=finalExt i ⟨p.val+2,by omega⟩)
    (hfinal:∀i,(data.P (index i).val).support=List.ofFn (finalExt i))
:
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∃(W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
      (u v:actualOldPieceIndex data→V) (q:∀z,(SimpleGraph.completeGraph V).Walk (u z) (v z))
      (g:{x // x∈data.prescribed}↪V) (f:{x // x∈A}↪V) (ψ:X→V),
      (∀z,W z∈M ∧ (W z).2.val=hub ∧ (W z).1.val 0=(π^z.2.val.val) (root z.1.1.val)) ∧
      (∀z,(q z).IsPath) ∧ (∀z,(q z).length=(actualOldPieceWalk data z).length) ∧
      (∀z z',z≠z'→Disjoint (q z).support.toFinset (q z').support.toFinset) ∧
      (∀j:{j // j∈data.t},∀x∈(q (.inl j)).support,x∈Ord) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀x∈(q (.inr r)).support,x∉Ord→
        ∃j:Fin (data.d+1),r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1 ∧ x=(π^j.val) (root r.1.val)) ∧
      (∀i (j:Fin (data.d+1)) (hj:bufferedMarker data.c data.d (ext i) j∈data.prescribed),
        g ⟨bufferedMarker data.c data.d (ext i) j,hj⟩=(π^j.val) (root i)) ∧
      (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
        f ⟨(actualOldPieceWalk data z).getVert k.val,
          Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
          (q z).getVert k.val) ∧
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X) ∧
      (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩) ∧ (∀x (hx:x∈data.prescribed),ψ x=g ⟨x,hx⟩) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
        ψ ((data.P r.1.val).getVert (2+data.c*(r.2.val.1+j)))=(π^(r.2.val.1+j)) (root r.1.val)) ∧
      (∀j:{j // j∈data.t},u (.inl j)=(C j).1.val (cycleNext 0) ∧ v (.inl j)=(C j).1.val 0) ∧
      (∀j:{j // j∈data.t},R (v (.inl j)) (u (.inl j))) ∧
      (∀j:{j // j∈data.t},∀k,k<(q (.inl j)).length→∃a:Fin (n j+1),
        (q (.inl j)).getVert k=(C j).1.val a ∧ (q (.inl j)).getVert (k+1)=(C j).1.val (cycleNext a)) ∧
      (∀z k,k<(q z).length→R ((q z).getVert k) ((q z).getVert (k+1))) ∧
      (∀r:SelectedRunIndex data.s₂ data.d data.T,∀e:Sym2 V,e∈(q (.inr r)).edges→∃z:actualSelectedSegmentIndex data,z.1=r ∧
        e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1):=by
  intro A
  obtain ⟨W,u,v,q,hW,hq,hlen,hqdis,hu,hv,hcy,hrun,hmarks,hends,hclose,hcedges,hdir,hedges⟩:=
    actual_mixed_packing_target_pieces data G tail head ktail khead m b hc π hb hπ H₀ Hₖ root hinj hdis M hub hpack hT Ord hOrd havoid n hn C hlenC hhubC hOrdC hCC hCM hE hK R hER hKR hCR
  obtain ⟨g,f,ψ,hg,hf,hψ,hψf,hψg⟩:=
    actual_matched_old_embedding_without_cross_hypothesis data hG hCycle ext hsupp hsrc index finalExt inner hinner hfinal π root hinj hdis Ord havoid (SimpleGraph.completeGraph V) u v q hq hlen hqdis hu hv hcy hrun hmarks
  have hparent:=matched_actual_run_preserves_parent_markers data (SimpleGraph.completeGraph V) u v q ψ f hψf hf π (fun i=>root i.val) hmarks
  exact ⟨W,u,v,q,g,f,ψ,hW,hq,hlen,hqdis,hcy,hrun,hg,hf,hψ,hψf,hψg,hparent,hends,hclose,hcedges,hdir,hedges⟩
end Oberwolfach
