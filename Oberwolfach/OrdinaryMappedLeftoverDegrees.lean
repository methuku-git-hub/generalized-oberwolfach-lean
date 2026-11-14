module

public import Oberwolfach.OrdinaryMappedCorrection

@[expose] public section
/-! An injective map preserves graph deletion and transfers a uniform
leftover-degree bound, with degree zero outside the image. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem ordinary_graph_map_sdiff (G D:SimpleGraph V) (φ:V↪W):
    (G\D).map φ=G.map φ\D.map φ:=by
  ext x y
  constructor
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj φ (G\D) x y).mp h
    refine ⟨SimpleGraph.map_adj_apply.mpr hab.1,?_⟩
    intro hd
    exact hab.2 (SimpleGraph.map_adj_apply.mp hd)
  · intro h
    obtain ⟨a,b,hab,rfl,rfl⟩:=(SimpleGraph.map_adj φ G x y).mp h.1
    apply SimpleGraph.map_adj_apply.mpr
    exact ⟨hab,fun hd=>h.2 (SimpleGraph.map_adj_apply.mpr hd)⟩

theorem ordinary_graph_map_degree_bound (G:SimpleGraph V) (φ:V↪W) (t:ℝ) (ht:0≤t)
    (hdegree:∀v,(G.degree v:ℝ)≤t):
    ∀w,((G.map φ).degree w:ℝ)≤t:=by
  intro w
  by_cases h:∃v,φ v=w
  · obtain ⟨v,rfl⟩:=h
    have hh:=hdegree v
    convert hh using 1
    exact_mod_cast SimpleGraph.degree_map_apply G φ v
  · have hz:((G.map φ).degree w:ℝ)=0:=by
      exact_mod_cast simpleGraph_map_degree_outside G φ w h
    rw [hz]
    exact ht
end Oberwolfach
