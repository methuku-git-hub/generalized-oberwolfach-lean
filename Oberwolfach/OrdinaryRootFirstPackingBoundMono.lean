module

public import Oberwolfach.OrdinaryRootFirstPackingContext

@[expose] public section
/-! Increasing the allowed packing error preserves the exact root cover,
    reserve and wheel family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def OrdinaryUnreservedPackingData.increaseBound
    {Q F:SimpleGraph V} {H:V→U→Prop} {X:Finset V} {Z:Finset U} {R:SimpleGraph (V⊕U)} {r:ℕ} {t t':ℝ}
    (M:OrdinaryUnreservedPackingData Q F H X Z R r t) (h:t≤t'):
    OrdinaryUnreservedPackingData Q F H X Z R r t' where
  wheels:=M.wheels
  disjoint:=M.disjoint
  leftover:=fun w=>(M.leftover w).trans h

def OrdinaryRootFirstPackingContext.increaseBound
    {Q F:SimpleGraph V} {H:V→U→Prop} {X T:Finset V} {Z W:Finset U} {r:ℕ} {η ell t t':ℝ}
    (K:OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t) (h:t≤t'):
    OrdinaryRootFirstPackingContext Q F H X T Z W r η ell t' where
  root_sub:=K.root_sub
  hub_sub:=K.hub_sub
  cover:=K.cover
  reserve:=K.reserve
  packing:=K.packing.increaseBound h
end Oberwolfach
