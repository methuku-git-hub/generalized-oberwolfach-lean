module

public import Oberwolfach.PrescribedPathEdgeEndpoints
public import Oberwolfach.PrescribedFreePathPhysicalEdges
public import Oberwolfach.PrescribedCyclePhysicalEdges

@[expose] public section
/-! Source edges of a component have endpoints in its new vertices or its
already assigned boundary vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_two_ended_component_endpoints (A:Finset X) (a b:X)
    (ha:a∈A) (hb:b∈A) (as:List X):
    ∀ e∈prescribedPathPhysicalEdges a b as,∀ x∈e.toFinset,x∈A∪as.toFinset := by
  intro e he x hx
  have hh:=prescribed_two_ended_edge_endpoints b as a e he x hx
  simp only [Finset.mem_insert] at hh
  rcases hh with hx'|hx'|hx'
  · subst x;exact Finset.mem_union_left _ ha
  · subst x;exact Finset.mem_union_left _ hb
  · exact Finset.mem_union_right _ hx'

theorem prescribed_one_ended_component_endpoints (A:Finset X) (a:X)
    (ha:a∈A) (as:List X):
    ∀ e∈prescribedOneSidedPhysicalEdges a as,∀ x∈e.toFinset,x∈A∪as.toFinset := by
  intro e he x hx
  have hh:=prescribed_one_ended_edge_endpoints as a e he x hx
  simp only [Finset.mem_insert] at hh
  rcases hh with hx'|hx'
  · subst x;exact Finset.mem_union_left _ ha
  · exact Finset.mem_union_right _ hx'

theorem prescribed_free_path_component_endpoints (as:List X):
    ∀ e∈prescribedFreePathPhysicalEdges as,∀ x∈e.toFinset,x∈as.toFinset := by
  cases as with
  | nil => intro e he;simp [prescribedFreePathPhysicalEdges] at he
  | cons a xs =>
    intro e he x hx
    have hh:=prescribed_one_ended_edge_endpoints xs a e he x hx
    simpa [List.toFinset_cons] using hh

theorem prescribed_free_cycle_component_endpoints (as:List X):
    ∀ e∈prescribedCyclePhysicalEdges as,∀ x∈e.toFinset,x∈as.toFinset := by
  cases as with
  | nil => intro e he;simp [prescribedCyclePhysicalEdges] at he
  | cons a xs =>
    intro e he x hx
    have hh:=prescribed_two_ended_edge_endpoints a xs a e he x hx
    simpa [List.toFinset_cons] using hh

theorem prescribed_pinned_cycle_component_endpoints (A:Finset X) (a:X)
    (ha:a∈A) (as:List X):
    ∀ e∈prescribedCyclePhysicalEdges (a::as),∀ x∈e.toFinset,x∈A∪as.toFinset := by
  exact prescribed_two_ended_component_endpoints A a a ha ha as
end Oberwolfach
