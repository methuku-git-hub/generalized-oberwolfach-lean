module

public import Oberwolfach.PrescribedOccurrenceUnion
public import Oberwolfach.PrescribedComponentLoadUpdate

@[expose] public section
/-! The exact free-occurrence counts retain their bound after adding an
injectively embedded component outside the currently saturated labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_actual_component_load_step (T C:Finset X) (f g:X→V) (t:ℝ)
    (hdis:Disjoint T C) (hpres:∀ x∈T,g x=f x) (hinj:Set.InjOn g C)
    (hbound:∀ v,((T.filter (fun x=>f x=v)).card:ℝ)≤t+1)
    (havoid:∀ x∈C,g x∉Finset.univ.filter (fun v=>(t:ℝ)≤(T.filter (fun y=>f y=v)).card)):
    ∀ v,(((T∪C).filter (fun x=>g x=v)).card:ℝ)≤t+1 := by
  let count:V→ℕ:=fun v=>(T.filter (fun x=>f x=v)).card
  have hdisS:Disjoint (C.image g) (Finset.univ.filter (fun v=>(t:ℝ)≤count v)):=by
    apply Finset.disjoint_left.mpr
    intro v hv hs
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    exact havoid x hx hs
  have hu:=prescribed_component_load_update count t (C.image g) hbound hdisS
  intro v
  have he:=prescribed_occurrence_union T C f g hdis hpres hinj v
  rw [he]
  exact hu v
end Oberwolfach
