module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! An injective component contributes exactly one occurrence at each of its
image vertices and zero occurrences elsewhere. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_component_occurrence_count (C:Finset X) (g:X→V)
    (hinj:Set.InjOn g C) (v:V):
    (C.filter (fun x=>g x=v)).card=(if v∈C.image g then 1 else 0) := by
  let T:=C.filter (fun x=>g x=v)
  change T.card=(if v∈C.image g then 1 else 0)
  have hle:T.card≤1:=by
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    have ha':=Finset.mem_filter.mp ha
    have hb':=Finset.mem_filter.mp hb
    exact hinj ha'.1 hb'.1 (ha'.2.trans hb'.2.symm)
  by_cases hv:v∈C.image g
  · obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hv
    have hpos:0<T.card:=Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hxv⟩⟩
    simp only [if_pos hv]
    omega
  · have hzero:T=∅:=by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hh:=Finset.mem_filter.mp hx
      exact hv (Finset.mem_image.mpr ⟨x,hh.1,hh.2⟩)
    simp [hv,hzero]
end Oberwolfach
