module

public import Oberwolfach.FiniteWalkExtension

@[expose] public section
/-! A finite walk and its stationary extension have the same edges at
all original indices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_walk_extension_initial_edges
    {V:Type*} {n:ℕ} (G:SimpleGraph V) (v:Fin (n+1)→V)
    (p:∀i:Fin n,G.Walk (v i.castSucc) (v i.succ)) (i:Fin n):
    (finiteWalkExtension G v p i).edges=(p i).edges := by
  simp only [finiteWalkExtension, dif_pos i.isLt, SimpleGraph.Walk.edges_copy]
end Oberwolfach
