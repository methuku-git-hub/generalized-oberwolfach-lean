module

public import Oberwolfach.GreedyGraphCandidates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance allGraphAdj {V:Type} (G:SimpleGraph V) : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _

theorem long_three_graph_degree_bound {V:Type} [Fintype V] [DecidableEq V]
  (A B C:SimpleGraph V) (v:V):
  (A⊔B⊔C).degree v≤A.degree v+B.degree v+C.degree v:=by
  have h₁:=graph_degree_sup_le A B v
  have h₂:=graph_degree_sup_le (A⊔B) C v
  simp only [← SimpleGraph.ncard_neighborSet] at h₁ h₂ ⊢
  omega
end Oberwolfach
