module

public import Oberwolfach.OrdinaryReservedFullTargetProtected

@[expose] public section
/-! A capacity bound for the whole inner set applies to each factor's
uncovered forced targets, since those targets lie in that same inner set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_inner_target_capacity
    {U V:Type} [Fintype U] [DecidableEq U] [DecidableEq V]
    (Inner:Finset V) (T Old:U→Finset V) (pres remaining:U→ℕ) (cost:ℕ)
    (hT:∀u,T u⊆Inner)
    (hcap:∀u,8*pres u+cost+4*Inner.card+10≤remaining u):
    ∀u,8*pres u+cost+4*(T u\Old u).card+10≤remaining u :=by
  intro u
  have hsub:T u\Old u⊆Inner:=fun x hx=>hT u (Finset.mem_sdiff.mp hx).1
  have hcard:=Finset.card_le_card hsub
  have h:=hcap u
  omega
end Oberwolfach
