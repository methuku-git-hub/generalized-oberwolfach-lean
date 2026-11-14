module

public import Oberwolfach.RegularCycleIsomorphism

@[expose] public section
/-! Transport an assigned component along the equality of its recorded hub
and the selected wheel's hub, without changing its vertex set or order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def factorComponentAtAssignedHub (F:U→SimpleGraph (Fin n))
    (z:Σu,(F u).ConnectedComponent) (u:U) (h:z.1=u):(F u).ConnectedComponent:=
  h ▸ z.2

theorem factor_component_at_assigned_hub_card (F:U→SimpleGraph (Fin n))
    (z:Σu,(F u).ConnectedComponent) (u:U) (h:z.1=u):
    Fintype.card (factorComponentAtAssignedHub F z u h)=Fintype.card z.2:=by
  rcases z with ⟨v,C⟩
  cases h
  rfl
end Oberwolfach
