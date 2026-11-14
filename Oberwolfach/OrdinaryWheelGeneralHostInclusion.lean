module

public import Oberwolfach.OrdinaryWheelFamilies

@[expose] public section
/-! Change both the rim and spoke host of a wheel while preserving its
physical resources and the indexed family graphs exactly. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [DecidableEq V] [DecidableEq U]
  {Q P F:SimpleGraph V} {H K:V→U→Prop} {r:ℕ}

def ordinaryWheelIncludeHost (hQP:Q≤P) (hHK:∀v u,H v u→K v u)
    (W:OrdinaryWheel Q F H r):OrdinaryWheel P F K r :=
  ⟨(⟨W.val.1.val,W.val.1.property.trans hQP⟩,W.val.2),
    (fun v hv=>hHK v W.val.2 (W.property.1 v hv)),W.property.2⟩

theorem ordinaryWheelIncludeHost_resources (hQP:Q≤P) (hHK:∀v u,H v u→K v u)
    (W:OrdinaryWheel Q F H r):
    ordinaryWheelResources (ordinaryWheelIncludeHost hQP hHK W)=ordinaryWheelResources W := rfl

theorem wheelFamily_includeHost_rim (hQP:Q≤P) (hHK:∀v u,H v u→K v u)
    (W:I→OrdinaryWheel Q F H r):
    wheelFamilyRim (fun i=>ordinaryWheelIncludeHost hQP hHK (W i))=wheelFamilyRim W := rfl

theorem wheelFamily_includeHost_spokes (hQP:Q≤P) (hHK:∀v u,H v u→K v u)
    (W:I→OrdinaryWheel Q F H r):
    wheelFamilySpokes (fun i=>ordinaryWheelIncludeHost hQP hHK (W i))=wheelFamilySpokes W := rfl
end Oberwolfach
