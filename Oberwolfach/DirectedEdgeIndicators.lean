module

public import Oberwolfach.MarkedCapacityPositionSplitting

@[expose] public section

/-! Incidence vectors of an actual directed edge, indexed by its ordered
endpoints. Endpoint injectivity is used explicitly, rather than identifying
physical and auxiliary edge sets. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def directedEdgeIndicator {V E : Type*} [DecidableEq V]
    (tail head : E → V) (x y : V) (e : E) : ℝ :=
  if tail e=x ∧ head e=y then 1 else 0

theorem directedEdgeIndicator_single {V E : Type*} [DecidableEq V]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e)))
    (e f : E) : directedEdgeIndicator tail head (tail e) (head e) f=
      if f=e then 1 else 0 := by
  classical
  have hi : tail f=tail e ∧ head f=head e ↔ f=e :=
    ⟨fun h => hinj (Prod.ext h.1 h.2),fun h => by subst f;exact ⟨rfl,rfl⟩⟩
  simp only [directedEdgeIndicator,hi]

theorem directedEdgeIndicator_total {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e)))
    (x y : V) (hxy : ∃ e,tail e=x ∧ head e=y) :
    (∑ e,directedEdgeIndicator tail head x y e)=1 := by
  classical
  obtain ⟨e,rfl,rfl⟩ := hxy
  simp only [directedEdgeIndicator_single tail head hinj]
  simp

theorem directedEdgeIndicator_tail {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e)))
    (x y : V) (hxy : ∃ e,tail e=x ∧ head e=y) (v : V) :
    occurrenceSumLinear tail (directedEdgeIndicator tail head x y) v=if x=v then 1 else 0 := by
  classical
  obtain ⟨e,rfl,rfl⟩ := hxy
  change (∑ f,if tail f=v then directedEdgeIndicator tail head (tail e) (head e) f else 0)=_
  simp only [directedEdgeIndicator_single tail head hinj]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp only [hfe,ite_false,ite_self]
  · simp

theorem directedEdgeIndicator_head {V E : Type*} [Fintype E] [DecidableEq V]
    (tail head : E → V) (hinj : Function.Injective (fun e => (tail e,head e)))
    (x y : V) (hxy : ∃ e,tail e=x ∧ head e=y) (v : V) :
    occurrenceSumLinear head (directedEdgeIndicator tail head x y) v=if y=v then 1 else 0 := by
  classical
  obtain ⟨e,rfl,rfl⟩ := hxy
  change (∑ f,if head f=v then directedEdgeIndicator tail head (tail e) (head e) f else 0)=_
  simp only [directedEdgeIndicator_single tail head hinj]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    simp only [hfe,ite_false,ite_self]
  · simp

end Oberwolfach
