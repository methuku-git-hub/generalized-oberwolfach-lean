module

public import Oberwolfach.FactorComponentAtAssignedHub

@[expose] public section
/-! Transporting a component to an equal hub preserves its actual vertices
and its internal adjacency. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

def factorComponentHubEquiv (F:U→SimpleGraph (Fin n))
    (z:Σu,(F u).ConnectedComponent) (u:U) (h:z.1=u):
    factorComponentAtAssignedHub F z u h ≃ z.2:=by
  rcases z with ⟨v,C⟩
  cases h
  exact Equiv.refl _

theorem factor_component_hub_equiv_vertex (F:U→SimpleGraph (Fin n))
    (z:Σu,(F u).ConnectedComponent) (u:U) (h:z.1=u)
    (x:factorComponentAtAssignedHub F z u h):
    (factorComponentHubEquiv F z u h x).val=x.val:=by
  rcases z with ⟨v,C⟩
  cases h
  rfl

theorem factor_component_hub_equiv_adj (F:U→SimpleGraph (Fin n))
    (z:Σu,(F u).ConnectedComponent) (u:U) (h:z.1=u)
    (x y:factorComponentAtAssignedHub F z u h):
    z.2.toSimpleGraph.Adj (factorComponentHubEquiv F z u h x) (factorComponentHubEquiv F z u h y) ↔
      (factorComponentAtAssignedHub F z u h).toSimpleGraph.Adj x y:=by
  rcases z with ⟨v,C⟩
  cases h
  rfl
end Oberwolfach
