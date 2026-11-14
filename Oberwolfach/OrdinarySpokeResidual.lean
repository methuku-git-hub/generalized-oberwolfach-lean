module

public import Oberwolfach.OrdinaryWheelLoads

@[expose] public section

/-! Once rim loads are exact, the degree balance makes each row of the
remaining spoke error sum to zero. This is the input for the all-pairs transfer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinarySpokeResidual {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (v : V) (u : U) : ℝ :=
  (if H v u then 1 else 0)-ordinarySpokeLoad ψ v u

theorem ordinarySpokeResidual_outside {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ) (v : V) (u : U) (hvu : ¬H v u) :
    ordinarySpokeResidual ψ v u=0 := by
  rw [ordinarySpokeResidual,if_neg hvu,ordinarySpokeLoad_eq_zero ψ v u hvu,sub_self]

theorem ordinarySpokeResidual_balanced {V U : Type*} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U]
    {Q F : SimpleGraph V} {H : V → U → Prop} {r : ℕ}
    (ψ : OrdinaryWheel Q F H r → ℝ)
    (hdeg : ∀ v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hR : ∀ x y,Q.Adj x y → ordinaryRimLoad ψ x y=1) (v : V) :
    (∑ u,ordinarySpokeResidual ψ v u)=0 := by
  have he (y : V) : ordinaryRimLoad ψ v y=if Q.Adj v y then 1 else 0 := by
    by_cases hvy : Q.Adj v y
    · rw [if_pos hvy];exact hR v y hvy
    · rw [if_neg hvy];exact ordinaryRimLoad_eq_zero ψ v y hvy
  have hb := ordinary_wheel_load_balance ψ v
  simp only [he] at hb
  have hsum : (∑ y,if Q.Adj v y then (1:ℝ) else 0)=(Q.degree v:ℝ) := graph_adjacency_row_sum Q v
  rw [hsum] at hb
  have hH : (∑ u,if H v u then (1:ℝ) else 0)=((Finset.univ.filter (H v)).card:ℝ) := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  have hd := congrArg (fun n : ℕ => (n:ℝ)) (hdeg v)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hd
  unfold ordinarySpokeResidual
  rw [Finset.sum_sub_distrib,hH]
  linarith

end Oberwolfach
