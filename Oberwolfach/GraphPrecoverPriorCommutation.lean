module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! Move a subset of a cover into an earlier deletion without changing
the final graph, provided the full cover is also deleted later. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem graph_precover_prior_commutation {V:Type} (G A B D R E:SimpleGraph V):
    ((G\A)\B)\D=(G\(B⊔((A\R)⊓E)))\(A⊔D):=by
  ext x y
  simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj,SimpleGraph.inf_adj]
  tauto
end Oberwolfach
