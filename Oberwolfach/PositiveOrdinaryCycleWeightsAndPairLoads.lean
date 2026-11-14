module

public import Oberwolfach.PositiveOrdinaryCycleWeights
public import Oberwolfach.OrdinaryCyclePairLoads

@[expose] public section

/-! The positive bounded cycle weighting and both physical pair-load bounds
hold simultaneously for the same weighting. These are the conclusions of
Theorem 8.2 needed by the ordinary wheel construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem positive_ordinary_cycle_weights_with_pair_loads
    (r : ℕ) (hr : 3 ≤ r) (α : ℝ) (hα : 0 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 0 < N ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ G : SimpleGraph V,
        (∀ v,(cycleThreshold r+α)*Fintype.card V ≤ (G.degree v:ℝ)) →
      ∃ a : OrdinaryCycle G r → ℝ,
        (∀ D,c/(Fintype.card V:ℝ)^(r-2) ≤ a D ∧
          a D ≤ C/(Fintype.card V:ℝ)^(r-2)) ∧
        (∀ e : G.edgeSet,∑ D,a D*ordinaryCycleIncidence G r D e=1) ∧
        (∀ x y z : V, x ≠ y → x ≠ z → y ≠ z →
          (∑ D,if D.val.val.Adj x y ∧ D.val.val.Adj x z then a D else 0) ≤
            C/Fintype.card V) ∧
        (∀ x y z t : V, x ≠ y → x ≠ z → x ≠ t → y ≠ z → y ≠ t → z ≠ t →
          (∑ D,if D.val.val.Adj x y ∧ D.val.val.Adj z t then a D else 0) ≤
            C/(Fintype.card V:ℝ)^2) := by
  obtain ⟨c,B,hc,hB,N,hN,hw⟩ := positive_ordinary_fractional_cycle_weights r hr α hα
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  let C := (r:ℝ)^4*B
  have hC : 0<C := by dsimp [C];positivity
  have hBC : B≤C := by
    dsimp [C]
    have hpow : (1:ℝ) ≤ (r:ℝ)^4 := one_le_pow₀ hrR
    nlinarith
  have hB3 : (r:ℝ)^3*B ≤ C := by
    dsimp [C]
    have hpow : (r:ℝ)^3 ≤ (r:ℝ)^4 := by nlinarith [sq_nonneg ((r:ℝ)^2)]
    exact mul_le_mul_of_nonneg_right hpow hB.le
  refine ⟨c,C,hc,hC,N,hN,?_⟩
  intro V _ _ hn G hdeg
  have hn0 : 0<Fintype.card V := hN.trans_le hn
  have hnR : (0:ℝ)≤Fintype.card V := Nat.cast_nonneg _
  obtain ⟨a,ha,hload⟩ := hw V hn G hdeg
  refine ⟨a,?_,hload,?_,?_⟩
  · intro D
    exact ⟨(ha D).1,(ha D).2.trans (div_le_div_of_nonneg_right hBC (by positivity))⟩
  · intro x y z hxy hxz hyz
    apply (ordinary_cycle_adjacent_pair_load G r (by omega) hn0 a
      (fun D => le_trans (by positivity) (ha D).1) B hB.le (fun D => (ha D).2)
      x y z hxy hxz hyz).trans
    exact div_le_div_of_nonneg_right hB3 hnR
  · intro x y z t hxy hxz hxt hyz hyt hzt
    apply (ordinary_cycle_disjoint_pair_load G r (by omega) hn0 a
      (fun D => le_trans (by positivity) (ha D).1) B hB.le (fun D => (ha D).2)
      x y z t hxy hxz hxt hyz hyt hzt).trans
    exact div_le_div_of_nonneg_right (le_refl C) (by positivity)

end Oberwolfach
