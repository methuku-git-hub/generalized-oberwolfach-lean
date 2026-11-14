module

public import Oberwolfach.OrdinaryLocalEndpointEventLift
public import Oberwolfach.OrdinaryFreshPhysicalEndpointEvent

@[expose] public section
/-! An inner-scale endpoint event supplies an ambient-scale event whenever
the latter's displayed tolerance fits inside the inner budget. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U K:Type} [Fintype V] [Fintype U] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq K]

theorem ordinary_local_endpoint_to_ambient_event
    (G F:SimpleGraph (V⊕U)) (T:Finset (V⊕U)) (S R:K→Finset (V⊕U))
    (g:K→(V⊕U)↪Sym2 (V⊕U)) (p ζlocal ζambient:ℝ) (hp:0≤p)
    (hscale:ζambient*Fintype.card (V⊕U)≤ζlocal*T.card) (σ:Sym2 (V⊕U)→Bool)
    (h:OrdinaryLocalEndpointEvent G F T S R g p ζlocal σ):
    OrdinaryFreshPhysicalEndpointEvent G F S R g p ζambient σ:=by
  intro k S' R' D hS hR hchangeS hchangeR hD hratio
  have hs:ζambient*(p*Fintype.card (V⊕U))≤ζlocal*(p*T.card):=by
    nlinarith only [mul_le_mul_of_nonneg_left hscale hp]
  exact h k S' R' D hS hR (hchangeS.trans hs) (hchangeR.trans hs)
    (fun v=>(hD v).trans hs) hratio
end Oberwolfach
