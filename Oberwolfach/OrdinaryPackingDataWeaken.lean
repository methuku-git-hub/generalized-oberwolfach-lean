module

public import Oberwolfach.OrdinaryPackingCleanupData

@[expose] public section
/-! A tighter actual leftover-degree bound can be used at any larger
cleanup threshold without changing the selected wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryPackingDataWeaken (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (R:SimpleGraph (V⊕U)) (r:ℕ) (t t':ℝ) (h:t≤t') (M:OrdinaryUnreservedPackingData Q F H X Z R r t):
    OrdinaryUnreservedPackingData Q F H X Z R r t' where
  wheels:=M.wheels
  disjoint:=M.disjoint
  leftover:=fun w=>(M.leftover w).trans h
end Oberwolfach
