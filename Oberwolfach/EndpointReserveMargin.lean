module

public import Oberwolfach.IntervalResidualMap
public import Oberwolfach.ReserveMargin

@[expose] public section

/-! The positive degree margin gives uniform slack on every existing
interface edge, with no change to the prescribed endpoint weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpointReserve_left_ratio {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (x : X) (y : Y) (D m : ℝ) (hD : 0 < D)
    (hQ : ∀ z, 0 ≤ Q x z) (hrow : ∑ z, Q x z = m)
    (hc : ∀ z, D ≤ (intervalCommon L R x z : ℝ)) :
    (∑ z, endpointReserve L R Q x y z) ≤ m / D := by
  calc
    (∑ z, endpointReserve L R Q x y z) ≤ ∑ z, Q x z / D := by
      apply Finset.sum_le_sum
      intro z _
      unfold endpointReserve
      split_ifs
      · exact div_le_div_of_nonneg_left (hQ z) hD (hc z)
      · exact div_nonneg (hQ z) hD.le
    _ = m / D := by rw [← Finset.sum_div, hrow]

theorem endpointReserve_left_margin {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (k δ α : ℝ) (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hα : 0 < α)
    (hthreshold : (k + (2 * k - 1) * α) * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (hQ : ∀ x z, 0 ≤ Q x z)
    (hrow : ∀ x, ∑ z, Q x z = (Finset.univ.filter (L x)).card / k)
    (x : X) (y : Y) :
    (∑ z, endpointReserve L R Q x y z) ≤
      (1 - (2 * k - 1) * α / k) * interfaceCapacity L x y := by
  have hdn : ((Finset.univ.filter (L x)).card : ℝ) ≤ Fintype.card Y := by
    exact_mod_cast Finset.card_le_univ (Finset.univ.filter (L x))
  obtain ⟨_, _, hden, hcap⟩ := reserve_capacity_positive_margin hk
    (by exact_mod_cast hn) hα hthreshold (hdL x) hdn ((hdL x).trans hdn)
  by_cases hxy : L x y
  · simp only [interfaceCapacity, hxy, ite_true, mul_one]
    apply le_trans (endpointReserve_left_ratio L R Q x y
      ((Finset.univ.filter (L x)).card + δ - Fintype.card Y)
      ((Finset.univ.filter (L x)).card / k) hden (hQ x) (hrow x) ?_) hcap
    intro z
    have hc : ((Finset.univ.filter (L x)).card : ℝ) +
        (Finset.univ.filter (fun y => R y z)).card ≤
        intervalCommon L R x z + Fintype.card Y := by
      exact_mod_cast intervalCommon_lower L R x z
    linarith [hdR z]
  · simp [endpointReserve, interfaceCapacity, hxy]

theorem endpointReserve_right_margin {X Y Z : Type*} [Fintype X] [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (k δ α : ℝ) (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hα : 0 < α)
    (hthreshold : (k + (2 * k - 1) * α) * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (hQ : ∀ x z, 0 ≤ Q x z)
    (hcol : ∀ z, ∑ x, Q x z = (Finset.univ.filter (fun y => R y z)).card / k)
    (y : Y) (z : Z) :
    (∑ x, endpointReserve L R Q x y z) ≤
      (1 - (2 * k - 1) * α / k) * interfaceCapacity R y z := by
  have hh := endpointReserve_left_margin (fun z y => R y z) (fun y x => L x y)
    (fun z x => Q x z) k δ α hk hn hα hthreshold hdR hdL (fun z x => hQ x z) hcol z y
  have heq (x : X) :
      endpointReserve (fun z y => R y z) (fun y x => L x y) (fun z x => Q x z) z y x =
        endpointReserve L R Q x y z := by
    simp only [endpointReserve, intervalCommon, and_comm]
  simpa only [heq, interfaceCapacity] using hh

end Oberwolfach
