module

public import Oberwolfach.VortexProtectedGeometry

@[expose] public section
/-! The first physical inner vertex set has the prescribed vortex scale. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_initial_inner_vertex_bound {V U:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] {G:SimpleGraph V} {D m:ℕ} {β ε:ℝ}
    (Q:Vortex U G D β ε m) (he:0≤ε):
    ((Q.extendedVertices 1).card:ℝ)≤ε*Fintype.card V:=by
  have hh:=(Q.extended_successor_size_bounds he 0).1
  simpa only [Nat.zero_add,Q.extendedVertices_eq (Nat.zero_le _),Q.initial,Finset.card_univ] using hh
end Oberwolfach
