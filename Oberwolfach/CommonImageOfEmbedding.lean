module

public import Oberwolfach.EndpointRelativeCounts

@[expose] public section
/-! Common-neighbour sets commute with relabelling a domain and its tests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {A B I J:Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [DecidableEq I] [DecidableEq J]

theorem common_image_of_maps (f:A→B) (g:I→J) (D:Finset A) (S:Finset I)
    (N:I→Finset A) (M:J→Finset B) (hmem:∀i x,x∈N i↔f x∈M (g i)):
    (common D S N).image f=common (D.image f) (S.image g) M:=by
  ext y
  constructor
  · intro hy
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
    have hx':= (mem_common_iff D S N x).mp hx
    apply (mem_common_iff (D.image f) (S.image g) M (f x)).mpr
    refine ⟨Finset.mem_image.mpr ⟨x,hx'.1,rfl⟩,?_⟩
    intro j hj
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hj
    exact (hmem i x).mp (hx'.2 i hi)
  · intro hy
    have hy':=(mem_common_iff (D.image f) (S.image g) M y).mp hy
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy'.1
    refine Finset.mem_image.mpr ⟨x,(mem_common_iff D S N x).mpr ⟨hx,?_⟩,rfl⟩
    intro i hi
    exact (hmem i x).mpr (hy'.2 (g i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩))
end Oberwolfach
