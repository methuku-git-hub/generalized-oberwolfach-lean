module

public import Oberwolfach.PrescribedComponentOccurrence

@[expose] public section
/-! Count all old and new free occurrences after one injective component
is added; previously assigned occurrences keep their images. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [DecidableEq X] [DecidableEq V]

theorem prescribed_occurrence_union (T C:Finset X) (f g:X→V)
    (hdis:Disjoint T C) (hpres:∀ x∈T,g x=f x) (hinj:Set.InjOn g C) (v:V):
    ((T∪C).filter (fun x=>g x=v)).card =
      (T.filter (fun x=>f x=v)).card+(if v∈C.image g then 1 else 0) := by
  have hT:T.filter (fun x=>g x=v)=T.filter (fun x=>f x=v):=by
    apply Finset.filter_congr
    intro x hx
    rw [hpres x hx]
  have hD:Disjoint (T.filter (fun x=>g x=v)) (C.filter (fun x=>g x=v)):=by
    exact hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [Finset.filter_union,Finset.card_union_of_disjoint hD,hT]
  rw [prescribed_component_occurrence_count C g hinj v]
end Oberwolfach
