module

public import Oberwolfach.PartialEmbeddingInteriorGlue

@[expose] public section
/-! Boundary agreement and avoidance of the reserved target set imply that
strict-path interior images do not collide with the complement map. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem interior_image_separated_by_boundary_and_avoidance
    {X Y:Type*} [DecidableEq X] [DecidableEq Y]
    (A D:Finset X) (hDA:D⊆A) (R:Finset Y)
    (fA:{x // x∈A}↪Y) (fC:{x // x∉D}→Y)
    (hbound:∀x (hx:x∈A) (hxD:x∉D),fA ⟨x,hx⟩=fC ⟨x,hxD⟩)
    (hinside:∀x (hx:x∈D),fA ⟨x,hDA hx⟩∈R)
    (havoid:∀x (hx:x∉D),x∉A→fC ⟨x,hx⟩∉R) :
    ∀x (hx:x∈D) y (hy:y∉D),fA ⟨x,hDA hx⟩≠fC ⟨y,hy⟩ := by
  intro x hx y hy heq
  by_cases hyA:y∈A
  · rw [←hbound y hyA hy] at heq
    have hxy:x=y:=congrArg Subtype.val (fA.injective heq)
    exact hy (hxy ▸ hx)
  · exact havoid y hy hyA (heq ▸ hinside x hx)
end Oberwolfach
