module

public import Oberwolfach.OrdinaryPotentialLoads
public import Oberwolfach.ResourceDecompositions

@[expose] public section
/-! Widening the rim host and spoke relation preserves a wheel's physical
resources and therefore preserves every exact resource decomposition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryWheelHostLift {P Q F:SimpleGraph V} {H K:V→U→Prop} {r:ℕ}
    (hPQ:P≤Q) (hHK:∀v u,H v u→K v u) (W:OrdinaryWheel P F H r):OrdinaryWheel Q F K r:=
  ⟨(⟨W.val.1.val,W.val.1.property.trans hPQ⟩,W.val.2),
    ⟨fun v hv=>hHK v _ (W.property.1 v hv),W.property.2⟩⟩

theorem ordinary_wheel_host_lift_resources {P Q F:SimpleGraph V} {H K:V→U→Prop} {r:ℕ}
    (hPQ:P≤Q) (hHK:∀v u,H v u→K v u) (W:OrdinaryWheel P F H r):
    ordinaryWheelResources (ordinaryWheelHostLift hPQ hHK W)=ordinaryWheelResources W:=by
  rfl

theorem ordinary_wheel_host_decomposition_lift {P Q F:SimpleGraph V} {H K:V→U→Prop} {r:ℕ}
    (hPQ:P≤Q) (hHK:∀v u,H v u→K v u) (S:Finset (Sym2 V⊕(V×U)))
    (hS:HasResourceDecomposition (ordinaryWheelResources (P:=P) (F:=F) (Hbase:=H) (r:=r)) S):
    HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=K) (r:=r)) S:=by
  exact resource_decomposition_map _ _ (ordinaryWheelHostLift hPQ hHK)
    (ordinary_wheel_host_lift_resources hPQ hHK) S hS
end Oberwolfach
