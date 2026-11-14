module

public import Oberwolfach.GraphDifferenceChangedDegree
public import Oberwolfach.OrdinaryEmbeddedPairDegrees

@[expose] public section
/-! Full symmetric-edit degrees are preserved when both rim graphs are
embedded into a larger physical vertex type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem simpleGraph_map_difference (φ:V↪W) (R Q:SimpleGraph V):
    (R\Q).map φ=(R.map φ)\(Q.map φ):=by
  ext a b
  constructor
  · intro h
    obtain ⟨v,w,hvw,rfl,rfl⟩:=(SimpleGraph.map_adj φ (R\Q) a b).mp h
    exact ⟨SimpleGraph.map_adj_apply.mpr hvw.1,fun he=>hvw.2 (SimpleGraph.map_adj_apply.mp he)⟩
  · intro h
    obtain ⟨v,w,hvw,rfl,rfl⟩:=(SimpleGraph.map_adj φ R a b).mp h.1
    exact SimpleGraph.map_adj_apply.mpr ⟨hvw,fun hq=>h.2 (SimpleGraph.map_adj_apply.mpr hq)⟩

end Oberwolfach
