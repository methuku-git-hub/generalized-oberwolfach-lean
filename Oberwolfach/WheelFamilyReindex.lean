module

public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section

/-! Reindexing a finite wheel family preserves its physical union. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {Q F:SimpleGraph V} {H:V→U→Prop} {r n m:ℕ}

def wheelFamilyReindex (C:Fin n→OrdinaryWheel Q F H r) (h:m=n) : Fin m→OrdinaryWheel Q F H r:=
  fun i=>C (finCongr h i)

theorem wheelFamilyReindex_rim (C:Fin n→OrdinaryWheel Q F H r) (h:m=n) :
    wheelFamilyRim (wheelFamilyReindex C h)=wheelFamilyRim C := by
  subst m;rfl

theorem wheelFamilyReindex_spokes (C:Fin n→OrdinaryWheel Q F H r) (h:m=n) :
    wheelFamilySpokes (wheelFamilyReindex C h)=wheelFamilySpokes C := by
  subst m;rfl

theorem wheelFamilyReindex_disjoint (C:Fin n→OrdinaryWheel Q F H r) (h:m=n)
    (hc:∀ i j,i≠j → Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) :
    ∀ i j,i≠j → Disjoint (ordinaryWheelResources (wheelFamilyReindex C h i))
      (ordinaryWheelResources (wheelFamilyReindex C h j)) := by
  subst m;exact hc

end Oberwolfach
