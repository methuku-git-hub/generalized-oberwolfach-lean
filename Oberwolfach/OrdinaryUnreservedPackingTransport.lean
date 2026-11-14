module

public import Oberwolfach.OrdinaryPackingCleanupData

@[expose] public section
/-! Transport actual packing data along exact equalities of its rim,
spoke and reserve hosts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_packing_transport
    (Q Q' F:SimpleGraph V) (H H':V→U→Prop) (X:Finset V) (Z:Finset U)
    (R R':SimpleGraph (V⊕U)) (r:ℕ) (t:ℝ)
    (hQ:Q=Q') (hH:H=H') (hR:R=R')
    (K:OrdinaryUnreservedPackingData Q F H X Z R r t):
    Nonempty (OrdinaryUnreservedPackingData Q' F H' X Z R' r t):=by
  subst Q'
  subst H'
  subst R'
  exact ⟨K⟩
end Oberwolfach
