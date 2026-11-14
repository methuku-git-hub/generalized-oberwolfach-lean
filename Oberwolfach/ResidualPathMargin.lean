module

public import Oberwolfach.EndpointReserveMargin
public import Oberwolfach.ResidualEndpoint

@[expose] public section

/-! Quantitative bounds for the residual path weights on every actual path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem residualLeft_two_sided {X Y Z : Type*} [Fintype Z]
    (A : X → Y → ℝ) (ρ : X → Y → Z → ℝ) (σ : ℝ)
    (hρ : ∀ x y z, 0 ≤ ρ x y z)
    (hc : ∀ x y, (∑ z, ρ x y z) ≤ (1 - σ) * A x y)
    (x : X) (y : Y) :
    σ * A x y ≤ residualLeft A ρ x y ∧ residualLeft A ρ x y ≤ A x y := by
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun z _ => hρ x y z)
  unfold residualLeft
  constructor <;> nlinarith [hc x y]

theorem residualRight_two_sided {X Y Z : Type*} [Fintype X]
    (A : Y → Z → ℝ) (ρ : X → Y → Z → ℝ) (σ : ℝ)
    (hρ : ∀ x y z, 0 ≤ ρ x y z)
    (hc : ∀ y z, (∑ x, ρ x y z) ≤ (1 - σ) * A y z)
    (y : Y) (z : Z) :
    σ * A y z ≤ residualRight A ρ y z ∧ residualRight A ρ y z ≤ A y z := by
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun x _ => hρ x y z)
  unfold residualRight
  constructor <;> nlinarith [hc y z]

set_option maxHeartbeats 800000 in
theorem interval_residual_path_two_sided {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (k δ α : ℝ) (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hα : 0 < α)
    (hcard : Fintype.card X = Fintype.card Y)
    (hthreshold : (k + (2 * k - 1) * α) * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (hdY : ∀ y, δ ≤ (Finset.univ.filter (fun x => L x y)).card)
    (hQ : Q ∈ transportMatrices
      (fun x => (Finset.univ.filter (L x)).card / k)
      (fun z => (Finset.univ.filter (fun y => R y z)).card / k))
    (x : X) (y : Y) (z : Z) (hxy : L x y) (hyz : R y z) :
    let σ := (2 * k - 1) * α / k
    let q := k / (2 * k - 1)
    σ ^ 2 / ((k - 1) * Fintype.card Y) ≤
      scaledResidualPath (interfaceCapacity L) (interfaceCapacity R)
        (endpointReserve L R Q) k x y z ∧
    scaledResidualPath (interfaceCapacity L) (interfaceCapacity R)
      (endpointReserve L R Q) k x y z ≤
        1 / ((k - 1) * σ * q * Fintype.card Y) := by
  let σ := (2 * k - 1) * α / k
  let q := k / (2 * k - 1)
  let ρ := endpointReserve L R Q
  have hk0 : 0 < k := by linarith
  have hfac : 0 < 2 * k - 1 := by linarith
  have hn' : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hn
  have hσ : 0 < σ := div_pos (mul_pos hfac hα) hk0
  have hq : 0 < q := div_pos hk0 hfac
  have hδ : q * Fintype.card Y ≤ δ := by
    change k / (2 * k - 1) * Fintype.card Y ≤ δ
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hfac).mpr
    have hh := mul_pos (mul_pos hfac hα) hn'
    nlinarith
  have hρ : ∀ x y z, 0 ≤ ρ x y z := endpointReserve_nonneg L R Q hQ.1
  have hcL := endpointReserve_left_margin L R Q k δ α hk hn hα hthreshold
    hdL hdR hQ.1 hQ.2.1
  have hcR := endpointReserve_right_margin L R Q k δ α hk hn hα hthreshold
    hdL hdR hQ.1 hQ.2.2
  have hL := residualLeft_two_sided (interfaceCapacity L) ρ σ hρ hcL
  have hR := residualRight_two_sided (interfaceCapacity R) ρ σ hρ hcR
  have hax := hL x y
  have hbz := hR y z
  simp only [interfaceCapacity, hxy, hyz, ite_true, mul_one] at hax hbz
  have hdlow : σ * q * Fintype.card Y ≤ ∑ a, residualLeft (interfaceCapacity L) ρ a y := by
    calc
      σ * q * Fintype.card Y ≤ σ * δ := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hδ hσ.le
      _ ≤ σ * (Finset.univ.filter (fun a => L a y)).card :=
        mul_le_mul_of_nonneg_left (hdY y) hσ.le
      _ = ∑ a, σ * interfaceCapacity L a y := by
        rw [← Finset.mul_sum, interfaceCapacity_column]
      _ ≤ ∑ a, residualLeft (interfaceCapacity L) ρ a y :=
        Finset.sum_le_sum (fun a _ => (hL a y).1)
  have hdup : (∑ a, residualLeft (interfaceCapacity L) ρ a y) ≤ Fintype.card Y := by
    calc
      _ ≤ ∑ a, interfaceCapacity L a y := Finset.sum_le_sum (fun a _ => (hL a y).2)
      _ = (Finset.univ.filter (fun a => L a y)).card := interfaceCapacity_column L y
      _ ≤ Fintype.card X := by exact_mod_cast Finset.card_le_univ _
      _ = Fintype.card Y := by rw [hcard]
  exact scaled_path_two_sided hσ hq hn' (by linarith)
    hax.1 hbz.1 hax.2 hbz.2 hdlow hdup

end Oberwolfach
