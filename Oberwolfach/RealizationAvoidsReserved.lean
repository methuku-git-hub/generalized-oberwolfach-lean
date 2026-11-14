module

public import Oberwolfach.MatchingPhysicalLift

@[expose] public section
/-! Physical realizations avoid every reserved resource avoided by their
underlying sampled resources. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem realization_avoids_reserved {C X Y W:Type} [DecidableEq C] [DecidableEq X] [DecidableEq Y]
    (M:Finset C) (Q:C→Finset X) (φ:X→Y) (lift:C→W) (B:W→Finset Y) (Reserve:Finset Y)
    (hphysical:∀c∈M,B (lift c)=(Q c).image φ)
    (havoid:Disjoint ((M.biUnion Q).image φ) Reserve):
    ∀c∈M,Disjoint (B (lift c)) Reserve :=by
  intro c hc
  rw [hphysical c hc]
  apply Finset.disjoint_left.mpr
  intro y hy hreserve
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
  have hbig:φ x∈(M.biUnion Q).image φ:=
    Finset.mem_image.mpr ⟨x,Finset.mem_biUnion.mpr ⟨c,hc,hx⟩,rfl⟩
  exact (Finset.disjoint_left.mp havoid) hbig hreserve
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem realization_resource_union {C X Y W:Type} [DecidableEq C] [DecidableEq X] [DecidableEq Y]
    (M:Finset C) (Q:C→Finset X) (φ:X→Y) (lift:C→W) (B:W→Finset Y)
    (hphysical:∀c∈M,B (lift c)=(Q c).image φ):
    (M.biUnion fun c=>B (lift c))=(M.biUnion Q).image φ :=by
  ext y
  simp only [Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨c,hc,hy⟩
    rw [hphysical c hc] at hy
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hy
    exact ⟨x,⟨c,hc,hx⟩,rfl⟩
  · rintro ⟨x,⟨c,hc,hx⟩,rfl⟩
    refine ⟨c,hc,?_⟩
    rw [hphysical c hc]
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
end Oberwolfach
