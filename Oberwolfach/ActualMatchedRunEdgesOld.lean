module

public import Oberwolfach.WalkEdgeImagesExact
public import Oberwolfach.ActualRunEdgesOld

@[expose] public section
/-! Every edge of the matched target run is in the actual old physical
packing of the same source factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_matched_run_edges_old
    {X V K J:Type} [Fintype X] [DecidableEq X] [DecidableEq V] [DecidableEq K] [DecidableEq J]
    {G:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) G)
    (r:SelectedRunIndex data.s₂ data.d data.T) (H:SimpleGraph V) {a b:V} (q:H.Walk a b) (ψ:X→V)
    (hlen:q.length=(data.path (.inr r)).length)
    (hmap:∀k,k≤(data.path (.inr r)).length→ψ ((data.path (.inr r)).getVert k)=q.getVert k):
    q.edges.toFinset⊆(data.deletedEdges\
      (Finset.univ.biUnion (fun i:{i // i∈data.s₁}=>(data.path (.inl i)).edges.toFinset))).image (Sym2.map ψ):=by
  have h:=walk_edge_images_exact G H (data.path (.inr r)) q ψ hlen hmap
  rw [←h]
  exact Finset.image_subset_image (actual_run_edges_old data r)
end Oberwolfach
