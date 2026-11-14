module

public import Oberwolfach.OrdinaryUnreservedGeometryData
public import Oberwolfach.OrdinaryEditedParentFromSample

@[expose] public section
/-! Put the earlier sampled reference event and the later reserve geometry
into the same parent input for the actual unreserved packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_unreserved_parent_data_from_sample
    (r:ℕ) (hr:3≤r) (k:ℕ)
    (α ω βsource βparent β b B h ζedit δ εsource εparent εstar η ξ ζreserve p ε binner c d:ℝ)
    (P Q F:SimpleGraph V) (H₀ H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (raw coins:Sym2 V→Bool) (σ:Sym2 (V⊕U)→Bool)
    (data:OrdinaryEditedSampleReferenceData r hr k α βsource βparent b B h ζedit δ εsource εparent d
      P Q F H₀ H raw coins)
    (geo:OrdinaryUnreservedGeometryData r k ω βparent β b B εparent εstar η ξ ζreserve p ε binner c
      Q F H X Z σ):
    Nonempty (OrdinaryUnreservedParentData r hr k α ω βparent β b B (h-ζedit) δ εparent εstar η
      ξ ζreserve p ε binner c P Q F H X Z σ):=by
  obtain ⟨fields⟩:=ordinary_edited_parent_fields_from_sample r hr k α βsource βparent b B h ζedit δ
    εsource εparent d P Q F H₀ H raw coins data
  exact ordinary_unreserved_parent_data_from_edited_fields r hr k α ω βparent β b B (h-ζedit) δ
    εparent εstar η ξ ζreserve p ε binner c P Q F H X Z σ data.graph_sub fields geo
end Oberwolfach
