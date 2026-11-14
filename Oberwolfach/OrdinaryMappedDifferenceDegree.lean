module

public import Oberwolfach.OrdinaryMappedLeftoverDegrees

@[expose] public section
/-! A maximum-degree bound for a graph difference survives any injective
mapping of its vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W:Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

theorem ordinary_mapped_difference_degree_bound (G D:SimpleGraph V) (φ:V↪W) (t:ℝ) (ht:0≤t)
    (hleft:∀v,(((G\D).degree v):ℝ)≤t):
    ∀w,((((G.map φ)\(D.map φ)).degree w):ℝ)≤t:=by
  have hm:=ordinary_graph_map_degree_bound (G\D) φ t ht (by
    intro v
    convert hleft v using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)
  intro w
  apply le_trans ?_ (hm w)
  have he:=congrArg (fun K:SimpleGraph W=>(K.degree w:ℝ)) (ordinary_graph_map_sdiff G D φ).symm
  convert le_of_eq he using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
