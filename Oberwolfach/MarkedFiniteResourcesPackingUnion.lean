module

public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! Adding a packing to prescribed arc and spoke resources commutes with
passing to their physical resource sets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}
  {m b:ℕ} {H₀ HK:V→U→Prop}
theorem marked_finite_resources_union_packing
    (A:Finset (E⊕K)) (S:Finset (V×U))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK)):
    markedFiniteResources tail head ktail khead π (A∪M.biUnion markedWheelArcs)
      (S∪M.biUnion markedWheelSpokePairs)=
      markedFiniteResources tail head ktail khead π A S ∪ M.biUnion markedWheelPhysicalResources:=by
  rw [←markedPackingResources_eq_finite tail head ktail khead π M]
  simp only [markedFiniteResources,Finset.image_union]
  ac_rfl
end Oberwolfach
