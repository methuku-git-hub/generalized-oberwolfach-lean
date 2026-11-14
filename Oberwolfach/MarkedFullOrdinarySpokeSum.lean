module

public import Oberwolfach.MarkedFullSpokeWeightedSum
public import Oberwolfach.TypedMarkedIncidenceIndicators

@[expose] public section
/-! An ordinary spoke occurs at exactly one nonzero position of a
separated marked cycle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V}

theorem marked_full_ordinary_spoke_weighted_sum
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (x:V) (u:U):
    (∑ W:MarkedWheel tail head ktail khead m π b (fun (_:V) (_:U)=>True) (fun _ _=>True),
      if Sum.inr (false,x,u)∈typedMarkedOccurrenceResources W then w W.1 else 0)=
    ∑ i:Fin m,∑ C:MarkedCycleTuple tail head ktail khead m π b,if C.val i.succ=x then w C else 0 := by
  rw [←Equiv.sum_comp markedFullWheelEquiv,Fintype.sum_prod_type]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [Finset.sum_eq_single u]
  · change (if Sum.inr (false,x,u)∈typedMarkedOccurrenceResources (markedFullWheel C u) then w C else 0)=_
    have hh:=markedWheel_spoke_typed_indicator (markedFullWheel C u) false x u
    change (if u=u then markedSpokeIndicator C.val false x else 0)=
      (if Sum.inr (false,x,u)∈typedMarkedOccurrenceResources (markedFullWheel C u) then (1:ℝ) else 0) at hh
    simp only [if_pos rfl,markedSpokeIndicator,Bool.false_eq_true,ite_false] at hh
    have hm:=congrArg (fun z:ℝ=>w C*z) hh
    simp only [Finset.mul_sum,mul_ite,mul_one,mul_zero] at hm
    exact hm.symm
  · intro v _ hv
    simp only [markedFullWheelEquiv,Equiv.coe_fn_mk,marked_full_spoke_mem,hv,false_and,ite_false]
  · simp
end Oberwolfach
