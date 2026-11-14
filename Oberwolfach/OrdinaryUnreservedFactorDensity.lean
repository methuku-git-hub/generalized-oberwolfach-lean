module

public import Oberwolfach.OrdinaryUnreservedFactorCardinality

@[expose] public section
/-! The selected reserved component fraction determines the exact density of
the unreserved source factor, with no rounding assumption. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_unreserved_factor_density
    {n r:ℕ} (F:SimpleGraph (Fin n)) (C:Finset F.ConnectedComponent)
    (hsize:∀c:↥C,Fintype.card c.val=r) (rsv:ℝ)
    (hres:(r:ℝ)*C.card=rsv*n):
    (Fintype.card {x:Fin n // F.connectedComponentMk x∉C}:ℝ)=(1-rsv)*n:=by
  have hc:=ordinary_unreserved_factor_cardinality F C hsize
  have hc':(Fintype.card {x:Fin n // F.connectedComponentMk x∉C}:ℝ)+(r:ℝ)*C.card=n:=by
    exact_mod_cast hc
  rw [hres] at hc'
  nlinarith
end Oberwolfach
