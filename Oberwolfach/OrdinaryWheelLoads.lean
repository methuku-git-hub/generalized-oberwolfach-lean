module

public import Oberwolfach.OrdinaryCycleIncidence

@[expose] public section

/-! An ordinary r-wheel consists of an actual r-cycle in Q and a hub in U.
Every spoke belongs to H, and its rim vertices are independent in F. The two
load maps keep rim edges and spoke edges in separate domains. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev OrdinaryWheel {V U : Type*} (Q F : SimpleGraph V) (H : V → U → Prop) (r : ℕ) :=
  {W : OrdinaryCycle Q r × U //
    (∀ v∈W.1.val.val.support,H v W.2) ∧
    (∀ v∈W.1.val.val.support,∀ w∈W.1.val.val.support,¬F.Adj v w)}

def ordinaryWheelRim {V U : Type*} {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : OrdinaryWheel Q F H r) : SimpleGraph V := W.val.1.val.val

def ordinaryWheelHub {V U : Type*} {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (W : OrdinaryWheel Q F H r) : U := W.val.2

def ordinaryRimLoad {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (x y : V) : ℝ :=
  ∑ W,if (ordinaryWheelRim W).Adj x y then ψ W else 0

def ordinarySpokeLoad {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (v : V) (u : U) : ℝ :=
  ∑ W,if ordinaryWheelHub W=u ∧ v∈(ordinaryWheelRim W).support then ψ W else 0

theorem ordinaryRimLoad_eq_zero {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (x y : V) (hxy : ¬Q.Adj x y) :
    ordinaryRimLoad ψ x y=0 := by
  apply Finset.sum_eq_zero
  intro W _
  exact if_neg (fun h => hxy (W.val.1.property h))

theorem ordinarySpokeLoad_eq_zero {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (v : V) (u : U) (hvu : ¬H v u) :
    ordinarySpokeLoad ψ v u=0 := by
  apply Finset.sum_eq_zero
  intro W _
  apply if_neg
  intro hh
  exact hvu (hh.1 ▸ W.property.1 v hh.2)

theorem embedded_cycle_weighted_row {V : Type*} [Fintype V] [DecidableEq V]
    {C : SimpleGraph V} {r : ℕ} (hC : IsEmbeddedCycle C r) (v : V) (a : ℝ) :
    (∑ y,if C.Adj v y then a else 0)=2*(if v∈C.support then a else 0) := by
  have he : (∑ y,if C.Adj v y then a else 0)=(C.degree v:ℝ)*a := by
    rw [← graph_adjacency_row_sum C v,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    split_ifs <;> simp
  rw [he]
  rcases hC.degree_zero_or_two v with hz|ht
  · have hv : v∉C.support := (C.degree_eq_zero_iff_notMem_support v).mp hz
    simp [hz,hv]
  · have hv : v∈C.support := by
      by_contra hn
      have hzero := (C.degree_eq_zero_iff_notMem_support v).mpr hn
      omega
    simp [ht,hv]

theorem finite_wheel_load_balance {V U W : Type*} [Fintype V] [Fintype U] [Fintype W]
    [DecidableEq V] [DecidableEq U] (C : W → SimpleGraph V) (hub : W → U)
    (r : ℕ) (hC : ∀ w,IsEmbeddedCycle (C w) r) (ψ : W → ℝ) (v : V) :
    2*(∑ u,∑ w,if hub w=u ∧ v∈(C w).support then ψ w else 0)=
      ∑ y,∑ w,if (C w).Adj v y then ψ w else 0 := by
  have hl : (∑ u : U,∑ w : W,if hub w=u ∧ v∈(C w).support then ψ w else 0)=
      ∑ w : W,∑ u : U,if hub w=u ∧ v∈(C w).support then ψ w else 0 := Finset.sum_comm
  have hr' : (∑ y : V,∑ w : W,if (C w).Adj v y then ψ w else 0)=
      ∑ w : W,∑ y : V,if (C w).Adj v y then ψ w else 0 := Finset.sum_comm
  rw [hl,hr',Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [embedded_cycle_weighted_row (hC w)]
  congr 1
  by_cases hv : v∈(C w).support
  · simp only [hv,and_true,ite_true]
    simp
  · simp only [hv,and_false,ite_false,Finset.sum_const_zero]

theorem ordinary_wheel_load_balance {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (v : V) :
    2*(∑ u,ordinarySpokeLoad ψ v u)=∑ y,ordinaryRimLoad ψ v y := by
  exact finite_wheel_load_balance ordinaryWheelRim ordinaryWheelHub r
    (fun W => W.val.1.val.property) ψ v

theorem ordinaryRimLoad_add {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ χ : OrdinaryWheel Q F H r → ℝ) (x y : V) :
    ordinaryRimLoad (ψ+χ) x y=ordinaryRimLoad ψ x y+ordinaryRimLoad χ x y := by
  unfold ordinaryRimLoad
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro W _
  simp only [Pi.add_apply]
  split_ifs <;> ring

theorem ordinarySpokeLoad_add {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ χ : OrdinaryWheel Q F H r → ℝ) (v : V) (u : U) :
    ordinarySpokeLoad (ψ+χ) v u=ordinarySpokeLoad ψ v u+ordinarySpokeLoad χ v u := by
  unfold ordinarySpokeLoad
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro W _
  simp only [Pi.add_apply]
  split_ifs <;> ring

end Oberwolfach
