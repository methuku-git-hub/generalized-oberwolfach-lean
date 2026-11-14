module

public import Oberwolfach.AveragedOrdinaryTransfer
public import Oberwolfach.OrdinaryRowCorrection

@[expose] public section

/-! Transfers between actual neighbouring hubs, with the diagonal equal to
zero. The configuration lower bound is required only for distinct hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryNeighbourTransfer {V U : Type*} [Fintype V]
    {r : ℕ} (hr : 3≤r) (Q F : SimpleGraph V) (H : V → U → Prop)
    (v : V) (i j : {u // H v u}) (D : OrdinaryWheel Q F H r) : ℝ :=
  if i.val=j.val then 0 else ordinaryAverageTransfer hr Q F H v i.val j.val D

theorem ordinaryNeighbourTransfer_loads {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {r : ℕ} (hr : 3≤r) (Q F : SimpleGraph V) (H : V → U → Prop)
    (v : V) (i j : {u // H v u})
    (hT : ∀ i j : {u // H v u},i.val≠j.val →
      0<Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val)) :
    (∀ x y,ordinaryRimLoad (ordinaryNeighbourTransfer hr Q F H v i j) x y=0) ∧
    (∀ z h,ordinarySpokeLoad (ordinaryNeighbourTransfer hr Q F H v i j) z h=
      (if z=v then (1:ℝ) else 0)*((if h=i.val then 1 else 0)-(if h=j.val then 1 else 0))) := by
  by_cases hij : i.val=j.val
  · constructor
    · intro x y
      simp [ordinaryNeighbourTransfer,hij,ordinaryRimLoad]
    · intro z h
      simp [ordinaryNeighbourTransfer,hij,ordinarySpokeLoad]
  · have he : ordinaryNeighbourTransfer hr Q F H v i j =
        ordinaryAverageTransfer hr Q F H v i.val j.val := by
      funext D
      exact if_neg hij
    rw [he]
    exact ordinaryAverageTransfer_loads hr Q F H v i.val j.val (hT i j hij)

theorem ordinaryNeighbourTransfer_bound {V U : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} (hr : 3≤r) (Q F : SimpleGraph V) (H : V → U → Prop)
    (v : V) (i j : {u // H v u}) (γ : ℝ) (hγ : 0<γ) (hn : 0<Fintype.card V)
    (hT : ∀ i j : {u // H v u},i.val≠j.val →
      γ*(Fintype.card V:ℝ)^(r^2)≤
        (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ))
    (D : OrdinaryWheel Q F H r) :
    |ordinaryNeighbourTransfer hr Q F H v i j D|≤
      if v∈(ordinaryWheelRim D).support then
        (6*((r:ℝ)^2)^r/γ)/(Fintype.card V:ℝ)^(r-1)
      else (6*((r:ℝ)^2)^r/γ)/(Fintype.card V:ℝ)^r := by
  by_cases hij : i.val=j.val
  · simp only [ordinaryNeighbourTransfer,if_pos hij,abs_zero]
    split_ifs <;> positivity
  · simpa only [ordinaryNeighbourTransfer,if_neg hij] using
      ordinaryAverageTransfer_coefficient_bound hr Q F H v i.val j.val γ hγ hn (hT i j hij) D

theorem ordinaryNeighbourTransfer_zero_other_hubs {V U : Type*} [Fintype V]
    {r : ℕ} (hr : 3≤r) (Q F : SimpleGraph V) (H : V → U → Prop)
    (v : V) (i j : {u // H v u}) (D : OrdinaryWheel Q F H r)
    (hi : ordinaryWheelHub D≠i.val) (hj : ordinaryWheelHub D≠j.val) :
    ordinaryNeighbourTransfer hr Q F H v i j D=0 := by
  unfold ordinaryNeighbourTransfer
  split_ifs
  · rfl
  · exact ordinaryAverageTransfer_zero_other_hubs hr Q F H v i.val j.val D hi hj

end Oberwolfach
