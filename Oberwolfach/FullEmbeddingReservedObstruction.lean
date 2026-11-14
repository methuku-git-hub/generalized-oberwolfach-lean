module

public import Oberwolfach.ActualOutsidePathAvoidance
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
/-! A whole-factor injection cannot avoid any target label when the source
and target have equal size. The outside-path restriction is essential. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem full_embedding_cannot_avoid_nonempty_reserved_set
    {X V:Type*} [Fintype X] [Fintype V] [DecidableEq V]
    (f:X→V) (hinj:Function.Injective f) (hcard:Fintype.card X=Fintype.card V)
    (Y:Finset V) (hY:Y.Nonempty):
    ¬Disjoint (Finset.univ.image f) Y:=by
  intro hdis
  obtain ⟨y,hy⟩:=hY
  obtain ⟨x,hx⟩:=((Fintype.bijective_iff_injective_and_card f).2 ⟨hinj,hcard⟩).2 y
  exact Finset.disjoint_left.mp hdis (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,hx⟩) hy
end Oberwolfach
