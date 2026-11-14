module

public import Oberwolfach.OrdinaryWheelLoads

@[expose] public section

/-! Signed indexed weights are aggregated onto actual wheel subgraphs.
The load equations remain valid when different indices describe the same wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def indexedWheelWeight {V U I : Type*} [Fintype I]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : I → OrdinaryWheel Q F H r) (a : I → ℝ) (D : OrdinaryWheel Q F H r) : ℝ :=
  ∑ i,if W i=D then a i else 0

theorem indexedWheelWeight_rim {V U I : Type*} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : I → OrdinaryWheel Q F H r) (a : I → ℝ) (x y : V) :
    ordinaryRimLoad (indexedWheelWeight W a) x y=
      ∑ i,a i*(if (ordinaryWheelRim (W i)).Adj x y then (1:ℝ) else 0) := by
  have hh := finite_marginal_test a W (indexedWheelWeight W a) (by
      intro D
      unfold indexedWheelWeight
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl)
    (fun D => if (ordinaryWheelRim D).Adj x y then (1:ℝ) else 0)
  rw [hh]
  unfold ordinaryRimLoad
  apply Finset.sum_congr rfl
  intro D _
  split_ifs <;> simp

theorem indexedWheelWeight_spoke {V U I : Type*} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : I → OrdinaryWheel Q F H r) (a : I → ℝ) (v : V) (u : U) :
    ordinarySpokeLoad (indexedWheelWeight W a) v u=
      ∑ i,a i*(if ordinaryWheelHub (W i)=u ∧ v∈(ordinaryWheelRim (W i)).support then (1:ℝ) else 0) := by
  have hh := finite_marginal_test a W (indexedWheelWeight W a) (by
      intro D
      unfold indexedWheelWeight
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> rfl)
    (fun D => if ordinaryWheelHub D=u ∧ v∈(ordinaryWheelRim D).support then (1:ℝ) else 0)
  rw [hh]
  unfold ordinarySpokeLoad
  apply Finset.sum_congr rfl
  intro D _
  split_ifs <;> simp

theorem indexedWheelWeight_fixed_hub {V U I : Type*} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : I → OrdinaryWheel Q F H r) (a : I → ℝ) (h : U)
    (hhub : ∀ i,ordinaryWheelHub (W i)=h) (v : V) (u : U) :
    ordinarySpokeLoad (indexedWheelWeight W a) v u=
      (if h=u then (1:ℝ) else 0)*
        ∑ i,a i*(if v∈(ordinaryWheelRim (W i)).support then (1:ℝ) else 0) := by
  rw [indexedWheelWeight_spoke,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hhub i]
  split_ifs <;> simp_all

theorem ordinaryRimLoad_sub {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ χ : OrdinaryWheel Q F H r → ℝ) (x y : V) :
    ordinaryRimLoad (ψ-χ) x y=ordinaryRimLoad ψ x y-ordinaryRimLoad χ x y := by
  unfold ordinaryRimLoad
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro W _
  simp only [Pi.sub_apply]
  split_ifs <;> ring

theorem ordinarySpokeLoad_sub {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ χ : OrdinaryWheel Q F H r → ℝ) (v : V) (u : U) :
    ordinarySpokeLoad (ψ-χ) v u=ordinarySpokeLoad ψ v u-ordinarySpokeLoad χ v u := by
  unfold ordinarySpokeLoad
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro W _
  simp only [Pi.sub_apply]
  split_ifs <;> ring

theorem indexed_wheel_transfer_loads {V U I : Type*} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W W' : I → OrdinaryWheel Q F H r) (a : I → ℝ) (v : V) (u u' : U)
    (hrim : ∀ i,ordinaryWheelRim (W i)=ordinaryWheelRim (W' i))
    (hhub : ∀ i,ordinaryWheelHub (W i)=u) (hhub' : ∀ i,ordinaryWheelHub (W' i)=u')
    (hvertex : ∀ z,(∑ i,a i*(if z∈(ordinaryWheelRim (W i)).support then (1:ℝ) else 0))=
      if z=v then 1 else 0) :
    (∀ x y,ordinaryRimLoad (indexedWheelWeight W a-indexedWheelWeight W' a) x y=0) ∧
    (∀ z h,ordinarySpokeLoad (indexedWheelWeight W a-indexedWheelWeight W' a) z h=
      (if z=v then (1:ℝ) else 0)*((if h=u then 1 else 0)-(if h=u' then 1 else 0))) := by
  constructor
  · intro x y
    rw [ordinaryRimLoad_sub,indexedWheelWeight_rim,indexedWheelWeight_rim]
    have he : (∑ i,a i*(if (ordinaryWheelRim (W i)).Adj x y then (1:ℝ) else 0))=
        ∑ i,a i*(if (ordinaryWheelRim (W' i)).Adj x y then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hrim i]
    rw [he,sub_self]
  · intro z h
    rw [ordinarySpokeLoad_sub,indexedWheelWeight_fixed_hub W a u hhub,
      indexedWheelWeight_fixed_hub W' a u' hhub',hvertex]
    have hv' : (∑ i,a i*(if z∈(ordinaryWheelRim (W' i)).support then (1:ℝ) else 0))=
        if z=v then 1 else 0 := by
      rw [← hvertex z]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrim i]
    rw [hv']
    simp only [eq_comm]
    ring

end Oberwolfach
