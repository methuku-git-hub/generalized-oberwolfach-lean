module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! Deleting physical rim and spoke edges commutes with forming the ordinary
physical graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinarySpokesAfterPhysicalDeletion (H:V→U→Prop) (K:SimpleGraph (V⊕U)):V→U→Prop:=
  fun v u=>H v u ∧ ¬K.Adj (Sum.inl v) (Sum.inr u)

theorem ordinary_physical_graph_after_deletion (Q:SimpleGraph V) (H:V→U→Prop)
    (K:SimpleGraph (V⊕U)):
    ordinaryPhysicalGraph (Q\K.comap Sum.inl) (ordinarySpokesAfterPhysicalDeletion H K)=
      ordinaryPhysicalGraph Q H\K:=by
  ext x y
  cases x with
  | inl v =>
    cases y with
    | inl w => rfl
    | inr u => rfl
  | inr u =>
    cases y with
    | inl v =>
      change (H v u ∧ ¬ K.Adj (Sum.inl v) (Sum.inr u)) ↔
        (H v u ∧ ¬ K.Adj (Sum.inr u) (Sum.inl v))
      rw [SimpleGraph.adj_comm K (Sum.inr u) (Sum.inl v)]
    | inr u' => simp [ordinaryPhysicalGraph]
theorem ordinary_rim_survives_of_physical_survives (Q Q':SimpleGraph V) (H H':V→U→Prop)
    (K:SimpleGraph (V⊕U))
    (h:ordinaryPhysicalGraph Q H\K≤ordinaryPhysicalGraph Q' H'):
    Q\K.comap Sum.inl≤Q':=by
  intro v w hvw
  exact h (v:=Sum.inl v) (w:=Sum.inl w) hvw
end Oberwolfach
