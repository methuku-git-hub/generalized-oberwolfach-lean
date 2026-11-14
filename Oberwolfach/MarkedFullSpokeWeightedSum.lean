module

public import Oberwolfach.MarkedPotentialSpokeAtHub

@[expose] public section
/-! The marked spoke at a fixed hub selects the zero position in the
underlying marked cycle, with its full multiplicity of cycle indices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}

theorem marked_cycle_true_vertex_mem (C:MarkedCycleTuple tail head ktail khead m π b) (x:V):
    (true,x)∈typedMarkedCycleVertices C ↔ C.val 0=x := by
  simp only [typedMarkedCycleVertices,Finset.mem_image,Finset.mem_univ,true_and,
    markedPositionType,Prod.mk.injEq,decide_eq_true_eq]
  constructor
  · rintro ⟨i,hi,hx⟩;subst i;exact hx
  · intro hx;exact ⟨0,rfl,hx⟩

theorem marked_full_spoke_weighted_sum
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (x:V) (u:U):
    (∑ W:MarkedWheel tail head ktail khead m π b (fun (_:V) (_:U)=>True) (fun _ _=>True),
      if Sum.inr (true,x,u)∈typedMarkedOccurrenceResources W then w W.1 else 0)=
    ∑ C,if C.val 0=x then w C else 0 := by
  rw [←Equiv.sum_comp markedFullWheelEquiv,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single u]
  · change (if Sum.inr (true,x,u)∈typedMarkedOccurrenceResources (markedFullWheel C u) then w C else 0)=_
    have hiff:Sum.inr (true,x,u)∈typedMarkedOccurrenceResources (markedFullWheel C u) ↔ C.val 0=x:=by
      rw [marked_full_spoke_mem,marked_cycle_true_vertex_mem]
      simp
    split_ifs <;> simp_all
  · intro v _ hv
    simp only [markedFullWheelEquiv,Equiv.coe_fn_mk,marked_full_spoke_mem,hv,false_and,ite_false]
  · simp
end Oberwolfach
