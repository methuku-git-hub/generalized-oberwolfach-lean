module

public import Oberwolfach.PrescribedActualLoadStep

@[expose] public section
/-! A component step preserves a second load invariant for any fixed set of
occurrences, provided its new selected images avoid that set's saturation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_restricted_component_load_step
    {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]
    (T C:Finset X) (select:X→Prop) (f g:X→V) (t:ℝ)
    (hdis:Disjoint T C) (hpres:∀x∈T,g x=f x) (hinj:Set.InjOn g C)
    (hbound:∀v,(((T.filter select).filter (fun x=>f x=v)).card:ℝ)≤t+1)
    (havoid:∀x∈C,select x→g x∉Finset.univ.filter
      (fun v=>(t:ℝ)≤((T.filter select).filter (fun y=>f y=v)).card)):
    ∀v,((((T∪C).filter select).filter (fun x=>g x=v)).card:ℝ)≤t+1 :=by
  have hdis':Disjoint (T.filter select) (C.filter select):=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hp:∀x∈T.filter select,g x=f x:=by
    intro x hx
    exact hpres x (Finset.mem_filter.mp hx).1
  have hi:Set.InjOn g (C.filter select):=hinj.mono (by
    intro x hx
    exact (Finset.mem_filter.mp hx).1)
  have ha:∀x∈C.filter select,g x∉Finset.univ.filter
      (fun v=>(t:ℝ)≤((T.filter select).filter (fun y=>f y=v)).card):=by
    intro x hx
    exact havoid x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have hh:=prescribed_actual_component_load_step (T.filter select) (C.filter select) f g t hdis' hp hi hbound ha
  intro v
  simpa only [Finset.filter_union] using hh v
end Oberwolfach
