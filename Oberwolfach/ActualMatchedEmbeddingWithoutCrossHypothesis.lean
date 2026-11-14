module

public import Oberwolfach.ActualAnchorCrossAvoidanceFromMarkers
public import Oberwolfach.ActualOldPieceMarkerPreimages
public import Oberwolfach.ActualOldMatchedEndpointEmbedding
public import Oberwolfach.ActualAnchorRunEndpoints
public import Oberwolfach.ActualPrescribedAnchorEmbedding

@[expose] public section
/-! Construct and glue the actual piece and anchor maps, deriving their cross
avoidance from the target marker geometry and ordinary-spoke exclusion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_old_embedding_without_cross_hypothesis
    {X V K J I:Type} [Fintype X] [DecidableEq X] [Fintype V] [DecidableEq V] [Nonempty V]
    [Fintype K] [DecidableEq K] [DecidableEq J] [Fintype I]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G) (hG:G.IsRegularOfDegree 2)
    (hCycle:data.t.biUnion (fun j=>(data.C j).support.toFinset)⊆data.Cembed)
    (ext:∀i:K,Fin (data.c*data.d+5)↪X)
    (hsupp:∀i∈data.s₁∪data.s₂,(data.P i).support=List.ofFn (ext i))
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (b:I≃{i // i∈data.s₁}) (finalExt:∀i:I,Fin (data.c*data.d+5)↪X)
    (inner:∀i:I,Fin (data.c*data.d+1)↪X)
    (hinner:∀i p,inner i p=finalExt i ⟨p.val+2,by omega⟩)
    (hfinal:∀i,(data.P (b i).val).support=List.ofFn (finalExt i))
    (π:Equiv.Perm V) (root:K→V)
    (hinj:∀i,Function.Injective (fun j:Fin (data.d+1)=>(π^j.val) (root i)))
    (hdis:∀i j,i≠j→Disjoint (permutationWindow π 0 data.d (root i)) (permutationWindow π 0 data.d (root j)))
    (Ord:Finset V) (hOrd:∀i,Disjoint (permutationWindow π 0 data.d (root i)) Ord)
    (H:SimpleGraph V) (u v:actualOldPieceIndex data→V)
    (q:∀z,H.Walk (u z) (v z)) (hq:∀z,(q z).IsPath)
    (hlen:∀z,(q z).length=(actualOldPieceWalk data z).length)
    (hqdis:∀z z',z≠z'→Disjoint (q z).support.toFinset (q z').support.toFinset)
    (hu:∀r:SelectedRunIndex data.s₂ data.d data.T,u (.inr r)=(π^r.2.val.1) (root r.1.val))
    (hv:∀r:SelectedRunIndex data.s₂ data.d data.T,v (.inr r)=(π^(r.2.val.2+1)) (root r.1.val))
    (hcycle:∀j:{j // j∈data.t},∀x∈(q (.inl j)).support,x∈Ord)
    (hrun:∀r:SelectedRunIndex data.s₂ data.d data.T,∀x∈(q (.inr r)).support,x∉Ord→
      ∃j:Fin (data.d+1),r.2.val.1≤j.val ∧ j.val≤r.2.val.2+1 ∧ x=(π^j.val) (root r.1.val))
    (hmarks:∀r:SelectedRunIndex data.s₂ data.d data.T,∀j,j≤r.2.val.2+1-r.2.val.1→
      (q (.inr r)).getVert (data.c*j)=(π^(r.2.val.1+j)) (root r.1.val)):
    let A:=Finset.univ.biUnion (fun z:actualOldPieceIndex data=>(actualOldPieceWalk data z).support.toFinset)
    ∃(g:{x // x∈data.prescribed}↪V) (f:{x // x∈A}↪V) (ψ:X→V),
      (∀i (j:Fin (data.d+1)) (hj:bufferedMarker data.c data.d (ext i) j∈data.prescribed),
        g ⟨bufferedMarker data.c data.d (ext i) j,hj⟩=(π^j.val) (root i)) ∧
      (∀z (k:Fin ((actualOldPieceWalk data z).length+1)),
        f ⟨(actualOldPieceWalk data z).getVert k.val,
          Finset.mem_biUnion.mpr ⟨z,Finset.mem_univ _,List.mem_toFinset.mpr ((actualOldPieceWalk data z).getVert_mem_support _)⟩⟩=
          (q z).getVert k.val) ∧
      Set.InjOn ψ (↑(data.oldDomain\bufferedPathStrictInterior (fun _=>data.c*data.d) inner):Set X) ∧
      (∀x (hx:x∈A),ψ x=f ⟨x,hx⟩) ∧ (∀x (hx:x∈data.prescribed),ψ x=g ⟨x,hx⟩):=by
  classical
  intro A
  obtain ⟨g,hg⟩:=actual_prescribed_anchor_embedding data ext hsupp hsrc π root hinj hdis
  have hends:=actual_anchor_values_on_run_endpoints data ext hsupp π root g hg
  obtain ⟨f,hf,hglue⟩:=actual_old_matched_embedding_from_endpoint_anchors data hG hCycle b finalExt inner hinner hfinal H u v q hq hlen hqdis
  have hpiece:=actual_old_piece_nonordinary_marker_preimages data ext hsupp π root Ord H u v q hcycle hrun hmarks f hf
  have hcross:=actual_anchor_cross_avoidance_from_marker_preimages data ext hsupp π root hinj hdis Ord hOrd A f g hg hpiece
  obtain ⟨ψ,hψ,hψf,hψg⟩:=hglue g (fun r hp=>(hends.1 r hp).trans (hu r).symm)
    (fun r hp=>(hends.2 r hp).trans (hv r).symm) hcross
  exact ⟨g,f,ψ,hg,hf,hψ,hψf,hψg⟩
end Oberwolfach
