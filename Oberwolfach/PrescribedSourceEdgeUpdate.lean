module

public import Oberwolfach.PrescribedPhysicalImagePreserved

@[expose] public section
/-! When all old source edges have assigned endpoints, updating the source
and physical edge sets by a new component preserves their exact image relation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_source_edge_update (A:Finset X) (f g:X→V)
    (hpres:∀ x∈A,g x=f x) (T C:Finset (Sym2 X))
    (hends:∀ e∈T,∀ x∈e.toFinset,x∈A):
    (T∪C).image (Sym2.map g)=(T.image (Sym2.map f))∪(C.image (Sym2.map g)) := by
  rw [Finset.image_union,prescribed_physical_image_preserved A f g hpres T hends]
end Oberwolfach
