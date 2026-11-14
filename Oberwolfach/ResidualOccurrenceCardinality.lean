module

public import Oberwolfach.LongPartitionedResidualDivisible

@[expose] public section
/-! Cardinalities of a finite residual arc set agree with the occurrence
counts used in the typed divisibility statement. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residual_occurrence_cardinality
    {V:Type} [Fintype V] [DecidableEq V]
    (P:V×V→Prop) (Q:Finset (V×V)) (hP:∀a,P a↔a∈Q) (f:V×V→V) (v:V):
    occurrenceDegree (fun e:{a:V×V // P a}=>f e.val) v =
      ((Q.filter (fun a=>f a=v)).card:ℝ):=by
  let e : {a:{a:V×V // P a} // f a.val=v} ≃ {a:V×V // a∈Q.filter (fun a=>f a=v)} := {
    toFun := fun x =>⟨x.val.val,Finset.mem_filter.mpr ⟨(hP _).mp x.val.property,x.property⟩⟩
    invFun := fun x =>⟨⟨x.val,(hP _).mpr (Finset.mem_filter.mp x.property).1⟩,(Finset.mem_filter.mp x.property).2⟩
    left_inv := by intro x; cases x; rfl
    right_inv := by intro x; cases x; rfl }
  have hc:=Fintype.card_congr e
  rw [Fintype.card_subtype] at hc
  have hc' : Fintype.card {a:V×V // a∈Q.filter (fun a=>f a=v)} = (Q.filter (fun a=>f a=v)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext a
    simp
  rw [hc'] at hc
  have hreal := congrArg (fun k:ℕ=>(k:ℝ)) hc
  have hsum : occurrenceDegree (fun e:{a:V×V // P a}=>f e.val) v =
      ((Finset.univ.filter (fun e:{a:V×V // P a}=>f e.val=v)).card:ℝ) := by
    unfold occurrenceDegree
    convert (Finset.sum_boole (R:=ℝ) (fun e:{a:V×V // P a}=>f e.val=v) Finset.univ) using 1 <;> congr!
  exact hsum.trans hreal
end Oberwolfach
