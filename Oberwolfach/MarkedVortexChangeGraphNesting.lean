module

public import Oberwolfach.MarkedVortexRestrictionChain

@[expose] public section
/-! The corrected physical change graphs on nested vortex levels are the
actual restrictions of one common pair of ambient graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_vortex_change_graph_nesting
    {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ} (Q:Vortex U G D β ε m)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (i j:ℕ) (hij:i≤j):
    FR.comap (markedVortexVertexEmbedding Q j)=
      (FR.comap (markedVortexVertexEmbedding Q i)).comap (markedVortexNestedVertex Q i j hij) ∧
    FS.comap (Sum.map (markedVortexVertexEmbedding Q j) (markedVortexHubEmbedding Q j))=
      (FS.comap (Sum.map (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i))).comap
        (Sum.map (markedVortexNestedVertex Q i j hij) (markedVortexNestedHub Q i j hij)):=by
  constructor
  · ext x y
    rfl
  · ext x y
    cases x <;> cases y <;> rfl
end Oberwolfach
