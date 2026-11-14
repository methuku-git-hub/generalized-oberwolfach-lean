module

public import Oberwolfach.MarkedPartitionedResidualDegrees

@[expose] public section
/-! Partitioning actual residual arcs by corrected type does not alter the
sum of occurrence degrees at any chosen physical endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [LinearOrder V]
local instance partitionedOccurrenceDecEq : DecidableEq V := Classical.decEq V
local instance partitionedOccurrenceArc (P:V×V→Prop):DecidableEq {e:V×V // P e}:=Classical.decEq _
local instance partitionedOccurrenceFinite (P:V×V→Prop):Fintype {e:V×V // P e}:=Fintype.ofFinite _
local instance partitionedOccurrenceOrdFinite (P:V×V→Prop) (M:Finset {e:V×V // P e}):Fintype (residualOrdinaryArc P M):=by
  change Fintype {e:{a:V×V // P a} // e∉M}
  exact Fintype.ofFinite _
local instance partitionedOccurrenceMarkFinite (P:V×V→Prop) (M:Finset {e:V×V // P e}):Fintype (residualMarkedArc P M):=by
  change Fintype {e:{a:V×V // P a} // e∈M}
  exact Fintype.ofFinite _

theorem partitioned_occurrence_degree_sum
    (P:V×V→Prop) (M:Finset {e:V×V // P e}) (f:{e:V×V // P e}→V) (v:V):
    occurrenceDegree (fun e:residualOrdinaryArc P M=>f e.val) v+
      occurrenceDegree (fun e:residualMarkedArc P M=>f e.val) v=occurrenceDegree f v:=by
  let eqv:residualOrdinaryArc P M⊕residualMarkedArc P M ≃ {e:V×V // P e}:={
    toFun:=Sum.elim Subtype.val Subtype.val
    invFun:=fun e=>if h:e∈M then Sum.inr ⟨e,h⟩ else Sum.inl ⟨e,h⟩
    left_inv:=by
      intro e
      cases e with
      | inl e=>simp only [Sum.elim_inl];simp [e.property]
      | inr e=>simp only [Sum.elim_inr];simp [e.property]
    right_inv:=by
      intro e
      by_cases h:e∈M <;> simp [h] }
  have hh:=Fintype.sum_equiv eqv (fun e:residualOrdinaryArc P M⊕residualMarkedArc P M=>
      if f (Sum.elim Subtype.val Subtype.val e)=v then (1:ℝ) else 0)
    (fun e:{e:V×V // P e}=>if f e=v then (1:ℝ) else 0) (by intro e;cases e <;> rfl)
  simpa only [occurrenceDegree,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] using hh
end Oberwolfach
