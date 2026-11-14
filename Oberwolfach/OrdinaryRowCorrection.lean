module

public import Oberwolfach.WheelLoadCombinations
public import Oberwolfach.SelectedPairTransfers

@[expose] public section

/-! Correcting one row of spoke errors by transfers between its actual
neighbouring hubs. The row sum hypothesis is proved from degree balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryRowCorrection {V U : Type*} [Fintype U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ} (v : V)
    (z : U → ℝ)
    (T : {u // H v u} → {u // H v u} → OrdinaryWheel Q F H r → ℝ)
    (W : OrdinaryWheel Q F H r) : ℝ :=
  ∑ p : {u // H v u} × {u // H v u},
    (z p.1.val/(Fintype.card {u // H v u}:ℝ))*T p.1 p.2 W

theorem ordinaryRowCorrection_loads {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ} (v : V)
    (z : U → ℝ) (hz : ∑ u : {u // H v u},z u.val=0)
    (hout : ∀ u,¬H v u → z u=0)
    (T : {u // H v u} → {u // H v u} → OrdinaryWheel Q F H r → ℝ)
    (hR : ∀ i j x y,ordinaryRimLoad (T i j) x y=0)
    (hS : ∀ i j x h,ordinarySpokeLoad (T i j) x h=
      (if x=v then (1:ℝ) else 0)*((if h=i.val then 1 else 0)-(if h=j.val then 1 else 0))) :
    (∀ x y,ordinaryRimLoad (ordinaryRowCorrection v z T) x y=0) ∧
    (∀ x h,ordinarySpokeLoad (ordinaryRowCorrection v z T) x h=
      (if x=v then (1:ℝ) else 0)*z h) := by
  constructor
  · intro x y
    unfold ordinaryRowCorrection
    rw [ordinaryRimLoad_combination]
    simp only [hR,mul_zero,Finset.sum_const_zero]
  · intro x h
    unfold ordinaryRowCorrection
    rw [ordinarySpokeLoad_combination]
    simp only [hS,Fintype.sum_prod_type]
    have he := selected_pair_transfer_identity (H v) z hz hout h
    calc
      _ = (if x=v then (1:ℝ) else 0)*
          ((∑ i : {u // H v u},∑ j : {u // H v u},
            z i.val*((if h=i.val then (1:ℝ) else 0)-(if h=j.val then 1 else 0)))/
            (Fintype.card {u // H v u}:ℝ)) := by
        simp only [Finset.sum_div,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [he]

end Oberwolfach
