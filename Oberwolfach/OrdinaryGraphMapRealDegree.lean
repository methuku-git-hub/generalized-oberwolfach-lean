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

theorem simpleGraph_map_real_degree_bound (φ:V↪W) (G:SimpleGraph V) (L:ℝ)
    (hL:0≤L) (hdeg:∀v,(G.degree v:ℝ)≤L):∀z,((G.map φ).degree z:ℝ)≤L:=by
  intro z
  by_cases hz:z∈Set.range φ
  · obtain ⟨v,rfl⟩:=hz
    have hh:=SimpleGraph.degree_map_apply G φ v
    have he:(G.map φ).degree (φ v)=G.degree v:=by
      simpa only [←SimpleGraph.ncard_neighborSet] using hh
    rw [he]
    exact hdeg v
  · rw [simpleGraph_map_degree_outside G φ z hz]
    simpa using hL

end Oberwolfach
