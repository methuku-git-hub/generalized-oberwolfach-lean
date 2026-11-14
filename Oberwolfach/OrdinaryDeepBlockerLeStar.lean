module

public import Oberwolfach.OrdinaryDeepBlockerNested
public import Oberwolfach.OrdinaryRootStarBoundaryZero

@[expose] public section
/-! The root star contains every edge inside the deeper induced pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deep_blocker_le_root_star (T:Finset V) (W:Finset U):
    ordinaryDeepBlocker T W≤ordinaryDeepRootStar T W:=by
  intro a b hab
  have hroot: a∈ordinaryInnerVertices T W:=
    (ordinary_deep_blocker_support_nested T T W W (Finset.Subset.refl _) (Finset.Subset.refl _) a b hab).1
  exact ordinary_edge_touching_deep_root_star (ordinaryDeepRimBlocker T) (ordinaryDeepSpokeBlocker T W)
    T W a b hab (Or.inl hroot)
end Oberwolfach
