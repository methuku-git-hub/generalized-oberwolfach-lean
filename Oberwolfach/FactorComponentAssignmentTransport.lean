module

public import Oberwolfach.FactorComponentAtAssignedHub

@[expose] public section
/-! Reindex an injective assignment by the prescribed hubs, retaining both
the components and their orders. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U A:Type} [Fintype U] [DecidableEq U]

theorem factor_component_at_assigned_hub_sigma (F:U→SimpleGraph (Fin n))
    (z:Σu,(F u).ConnectedComponent) (u:U) (h:z.1=u):
    (⟨u,factorComponentAtAssignedHub F z u h⟩:Σu,(F u).ConnectedComponent)=z:=by
  rcases z with ⟨v,C⟩
  cases h
  rfl

theorem factor_component_assignment_transport
    (F:U→SimpleGraph (Fin n)) (hub:A→U) (r:A→ℕ)
    (assign:A↪(Σu,(F u).ConnectedComponent))
    (hhub:∀a,(assign a).1=hub a)
    (hsize:∀a,Fintype.card (assign a).2=r a):
    ∃C:∀a,(F (hub a)).ConnectedComponent,
      (∀a,Fintype.card (C a)=r a) ∧
      (∀a,(⟨hub a,C a⟩:Σu,(F u).ConnectedComponent)=assign a) ∧
      Function.Injective (fun a=>(⟨hub a,C a⟩:Σu,(F u).ConnectedComponent)) :=by
  let C:=fun a=>factorComponentAtAssignedHub F (assign a) (hub a) (hhub a)
  have hC:∀a,(⟨hub a,C a⟩:Σu,(F u).ConnectedComponent)=assign a:=by
    intro a
    exact factor_component_at_assigned_hub_sigma F (assign a) (hub a) (hhub a)
  refine ⟨C,?_,hC,?_⟩
  · intro a
    rw [factor_component_at_assigned_hub_card]
    exact hsize a
  · intro a b hab
    apply assign.injective
    simpa only [hC] using hab
end Oberwolfach
