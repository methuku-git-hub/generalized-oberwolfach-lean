module

public import Oberwolfach.TransportMatrices

@[expose] public section

/-! The universal endpoint reserve for two consecutive interfaces. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserve_capacity_inequality {k n δ d : ℝ}
    (hk : 2 ≤ k) (hn : 0 < n) (_hδ : 0 ≤ δ)
    (hthreshold : k * n ≤ (2 * k - 1) * δ) (hd : δ ≤ d) :
    0 < d + δ - n ∧ (d / k) / (d + δ - n) ≤ 1 := by
  have hk0 : 0 < k := by linarith
  have hhalf : n < 2 * δ := by
    by_contra h
    have hh : 2 * δ ≤ n := le_of_not_gt h
    have hp := mul_nonneg (by linarith : 0 ≤ k - 1 / 2) (sub_nonneg.mpr hh)
    nlinarith
  have hden : 0 < d + δ - n := by linarith
  refine ⟨hden, (div_le_one hden).mpr ?_⟩
  apply (div_le_iff₀ hk0).mpr
  have hp := mul_nonneg (by linarith : 0 ≤ k - 1) (sub_nonneg.mpr hd)
  nlinarith

def intervalCommon {X Y Z : Type*} [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (x : X) (z : Z) : ℕ :=
  (Finset.univ.filter (fun y => L x y ∧ R y z)).card

def endpointReserve {X Y Z : Type*} [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (x : X) (y : Y) (z : Z) : ℝ :=
  if L x y ∧ R y z then Q x z / intervalCommon L R x z else 0

theorem endpointReserve_nonneg {X Y Z : Type*} [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (hQ : ∀ x z, 0 ≤ Q x z) (x : X) (y : Y) (z : Z) :
    0 ≤ endpointReserve L R Q x y z := by
  unfold endpointReserve
  split_ifs
  · exact div_nonneg (hQ x z) (Nat.cast_nonneg _)
  · exact le_refl _

theorem endpointReserve_endpoints {X Y Z : Type*} [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (hc : ∀ x z, 0 < intervalCommon L R x z) (x : X) (z : Z) :
    (∑ y, endpointReserve L R Q x y z) = Q x z := by
  unfold endpointReserve
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change (intervalCommon L R x z : ℝ) * (Q x z / intervalCommon L R x z) = _
  exact mul_div_cancel₀ _ (by exact_mod_cast (hc x z).ne')

theorem intervalCommon_lower {X Y Z : Type*} [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (x : X) (z : Z) :
    (Finset.univ.filter (L x)).card + (Finset.univ.filter (fun y => R y z)).card ≤
      intervalCommon L R x z + Fintype.card Y := by
  let A := Finset.univ.filter (L x)
  let B := Finset.univ.filter (fun y => R y z)
  have hc := Finset.card_union_add_card_inter A B
  have hu : (A ∪ B).card ≤ Fintype.card Y := Finset.card_le_univ _
  have hi : A ∩ B = Finset.univ.filter (fun y => L x y ∧ R y z) := by
    ext y
    simp only [A, B, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold intervalCommon
  rw [hi] at hc
  dsimp only [A, B] at hc hu
  omega

theorem endpointReserve_left_le {X Y Z : Type*} [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (dX : X → ℝ) (k δ : ℝ)
    (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hδ : 0 ≤ δ)
    (hthreshold : k * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hQ : ∀ x z, 0 ≤ Q x z)
    (hrow : ∀ x, ∑ z, Q x z = dX x / k)
    (hdX : ∀ x, dX x = (Finset.univ.filter (L x)).card)
    (hd : ∀ x, δ ≤ dX x)
    (hdR : ∀ z, δ ≤ (Finset.univ.filter (fun y => R y z)).card)
    (x : X) (y : Y) :
    (∑ z, endpointReserve L R Q x y z) ≤ 1 := by
  have hn' : (0 : ℝ) < Fintype.card Y := by exact_mod_cast hn
  obtain ⟨hden, hcap⟩ := reserve_capacity_inequality hk hn' hδ hthreshold (hd x)
  have hbound (z : Z) :
      endpointReserve L R Q x y z ≤ Q x z / (dX x + δ - Fintype.card Y) := by
    have hc := intervalCommon_lower L R x z
    have hc' : dX x + (Finset.univ.filter (fun y => R y z)).card ≤
        (intervalCommon L R x z : ℝ) + Fintype.card Y := by
      rw [hdX x]
      exact_mod_cast hc
    have hdenle : dX x + δ - Fintype.card Y ≤ (intervalCommon L R x z : ℝ) := by
      linarith [hdR z]
    unfold endpointReserve
    split_ifs
    · exact div_le_div_of_nonneg_left (hQ x z) hden hdenle
    · exact div_nonneg (hQ x z) hden.le
  calc
    (∑ z, endpointReserve L R Q x y z) ≤
        ∑ z, Q x z / (dX x + δ - Fintype.card Y) :=
      Finset.sum_le_sum fun z _ => hbound z
    _ = (dX x / k) / (dX x + δ - Fintype.card Y) := by rw [← Finset.sum_div, hrow x]
    _ ≤ 1 := hcap

theorem endpointReserve_right_le {X Y Z : Type*} [Fintype X] [Fintype Y]
    (L : X → Y → Prop) (R : Y → Z → Prop) (Q : X → Z → ℝ)
    (dZ : Z → ℝ) (k δ : ℝ)
    (hk : 2 ≤ k) (hn : 0 < Fintype.card Y) (hδ : 0 ≤ δ)
    (hthreshold : k * Fintype.card Y ≤ (2 * k - 1) * δ)
    (hQ : ∀ x z, 0 ≤ Q x z)
    (hcol : ∀ z, ∑ x, Q x z = dZ z / k)
    (hdZ : ∀ z, dZ z = (Finset.univ.filter (fun y => R y z)).card)
    (hd : ∀ z, δ ≤ dZ z)
    (hdL : ∀ x, δ ≤ (Finset.univ.filter (L x)).card)
    (y : Y) (z : Z) :
    (∑ x, endpointReserve L R Q x y z) ≤ 1 := by
  have hh := endpointReserve_left_le (fun z y => R y z) (fun y x => L x y)
    (fun z x => Q x z) dZ k δ hk hn hδ hthreshold (fun z x => hQ x z)
    hcol hdZ hd hdL z y
  have heq (x : X) :
      endpointReserve (fun z y => R y z) (fun y x => L x y) (fun z x => Q x z) z y x =
      endpointReserve L R Q x y z := by
    simp only [endpointReserve, intervalCommon, and_comm]
  simpa only [heq] using hh

theorem endpointReserve_continuous {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z]
    (L : X → Y → Prop) (R : Y → Z → Prop) :
    Continuous (fun Q : X → Z → ℝ => endpointReserve L R Q) := by
  apply continuous_pi
  intro x
  apply continuous_pi
  intro y
  apply continuous_pi
  intro z
  unfold endpointReserve
  split_ifs <;> fun_prop

end Oberwolfach
