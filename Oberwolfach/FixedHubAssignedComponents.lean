module

public import Oberwolfach.FactorComponentAssignmentTransport

@[expose] public section
/-! For a fixed hub, an injective assignment selects distinct actual
components of that hub's prescribed factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U A:Type} [Fintype U] [DecidableEq U]

theorem fixed_hub_assigned_components_injective
    (F:U→SimpleGraph (Fin n)) (hub:A→U)
    (C:∀a,(F (hub a)).ConnectedComponent)
    (assign:A↪(Σu,(F u).ConnectedComponent))
    (hC:∀a,(⟨hub a,C a⟩:Σu,(F u).ConnectedComponent)=assign a)
    (u:U):
    let B:Type:={a:A // hub a=u}
    let D:B→(F u).ConnectedComponent:=fun a=>
      factorComponentAtAssignedHub F ⟨hub a.val,C a.val⟩ u a.property
    Function.Injective D :=by
  intro B D a b hab
  have ha:(⟨u,D a⟩:Σu,(F u).ConnectedComponent)=assign a.val:=by
    exact (factor_component_at_assigned_hub_sigma F ⟨hub a.val,C a.val⟩ u a.property).trans (hC a.val)
  have hb:(⟨u,D b⟩:Σu,(F u).ConnectedComponent)=assign b.val:=by
    exact (factor_component_at_assigned_hub_sigma F ⟨hub b.val,C b.val⟩ u b.property).trans (hC b.val)
  apply Subtype.ext
  apply assign.injective
  rw [←ha,←hb,hab]
end Oberwolfach
