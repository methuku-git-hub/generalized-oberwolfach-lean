module

public import Oberwolfach.FactorComponentAssignmentTransport

@[expose] public section
/-! An injective assignment to actual factor components gives disjoint
source vertex sets for different selected candidates at the same hub. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U A:Type} [Fintype U] [DecidableEq U]

theorem assigned_factor_component_source_disjoint
    (F:U→SimpleGraph (Fin n)) (hub:A→U)
    (C:∀a,(F (hub a)).ConnectedComponent)
    (assign:A↪(Σu,(F u).ConnectedComponent))
    (hC:∀a,(⟨hub a,C a⟩:Σu,(F u).ConnectedComponent)=assign a):
    ∀a a',a≠a'→hub a=hub a'→Disjoint (C a).supp (C a').supp :=by
  intro a a' hne heq
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have h1:(F (hub a)).connectedComponentMk x=C a:=hx
  have h2:(F (hub a')).connectedComponentMk x=C a':=hx'
  have hA:assign a=(⟨hub a,(F (hub a)).connectedComponentMk x⟩:Σu,(F u).ConnectedComponent):=by
    rw [←hC a,h1]
  have hB:assign a'=(⟨hub a',(F (hub a')).connectedComponentMk x⟩:Σu,(F u).ConnectedComponent):=by
    rw [←hC a',h2]
  have hsame:(⟨hub a,(F (hub a)).connectedComponentMk x⟩:Σu,(F u).ConnectedComponent)=
      ⟨hub a',(F (hub a')).connectedComponentMk x⟩:=by rw [heq]
  exact hne (assign.injective (hA.trans (hsame.trans hB.symm)))
end Oberwolfach
