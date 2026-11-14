module

public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! Every rim edge belongs to the corresponding physical rim-and-spoke host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_rim_inside (Q:SimpleGraph V) (H:V→U→Prop):
    Q.map (Function.Embedding.inl:V↪V⊕U)≤ordinaryPhysicalGraph Q H:=by
  rw [graph_map_inl_physical]
  intro x y h
  cases x <;> cases y <;> simpa [ordinaryPhysicalGraph] using h
end Oberwolfach
