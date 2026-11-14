module

public import Oberwolfach.OrdinaryInducedFinsetTransfer

@[expose] public section
/-! Endpoint row and codegree counts are unchanged by restricting the
physical graph to a domain containing the endpoint classes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W:Type} [Fintype W] [DecidableEq W]

theorem ordinary_induced_endpoint_neighbor_card (G:SimpleGraph W) (T S:Finset W)
    (hST:S⊆T) (v:{v:W // v∈T}):
    ((ordinaryInducedFinset T S)∩(G.induce (T:Set W)).neighborFinset v).card=
      (S∩G.neighborFinset v.val).card:=by
  have hs:ordinaryInducedFinset T (S∩G.neighborFinset v.val)=
      (ordinaryInducedFinset T S)∩(G.induce (T:Set W)).neighborFinset v:=by
    ext x
    simp only [ordinaryInducedFinset,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter,
      SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj]
  rw [←hs]
  exact ordinary_induced_finset_card T _ (Finset.inter_subset_left.trans hST)

theorem ordinary_induced_endpoint_codegree_card (G:SimpleGraph W) (T S:Finset W)
    (hST:S⊆T) (v w:{v:W // v∈T}):
    (((ordinaryInducedFinset T S)∩(G.induce (T:Set W)).neighborFinset v)∩
      (G.induce (T:Set W)).neighborFinset w).card=
      ((S∩G.neighborFinset v.val)∩G.neighborFinset w.val).card:=by
  have hs:ordinaryInducedFinset T ((S∩G.neighborFinset v.val)∩G.neighborFinset w.val)=
      ((ordinaryInducedFinset T S)∩(G.induce (T:Set W)).neighborFinset v)∩
        (G.induce (T:Set W)).neighborFinset w:=by
    ext x
    simp only [ordinaryInducedFinset,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter,
      SimpleGraph.mem_neighborFinset,SimpleGraph.induce_adj]
  rw [←hs]
  exact ordinary_induced_finset_card T _ (Finset.inter_subset_left.trans (Finset.inter_subset_left.trans hST))
end Oberwolfach
