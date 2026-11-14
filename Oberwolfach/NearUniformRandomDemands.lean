module

public import Oberwolfach.BipartiteDegreeRounding
public import Oberwolfach.FractionalDegrees

@[expose] public section

/-! Near-uniform integer demands with a bounded marginal probability for
every edge. The law is obtained from real flow followed by exact rounding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem nearUniform_random_demands {X Y E : Type*}
    [Fintype X] [Fintype Y] [Fintype E] [DecidableEq E] [DecidableEq X] [DecidableEq Y]
    (tail : E → X) (head : E → Y) (f : X → ℕ) (g : Y → ℕ)
    (δ M h p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (ha : 0 < Fintype.card X) (hb : 0 < Fintype.card Y)
    (hδ : 0 ≤ δ) (hδsmall : δ < 1 / 4) (hM : 0 ≤ M)
    (hMC : M / p ≤ h * Fintype.card X * Fintype.card Y / 2)
    (hftotal : ∑ x, (f x : ℝ) = M) (hgtotal : ∑ y, (g y : ℝ) = M)
    (hf : ∀ x, (f x : ℝ) ≤ (1 + δ) * M / Fintype.card X)
    (hg : ∀ y, (g y : ℝ) ≤ (1 + δ) * M / Fintype.card Y)
    (hlarge : ∀ (S : Finset X) (T : Finset Y),
      1 - 2 * δ < (S.card : ℝ) / Fintype.card X + (T.card : ℝ) / Fintype.card Y →
      h * Fintype.card X * Fintype.card Y *
        min ((S.card : ℝ) / Fintype.card X) ((T.card : ℝ) / Fintype.card Y) ≤
      ((Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ T)).card : ℝ)) :
    ∃ ν : FiniteLaw (E → Bool),
      (∀ D, 0 < ν.mass D →
        (∀ x, (∑ e, if tail e = x ∧ D e = true then (1 : ℕ) else 0) = f x) ∧
        (∀ y, (∑ e, if head e = y ∧ D e = true then (1 : ℕ) else 0) = g y)) ∧
      (∀ e, ν.probability (fun D => D e = true) ≤ p) := by
  obtain ⟨q, hq, hleft, hright⟩ := bipartite_nearUniformFractionalDegrees
    tail head (fun x => f x / p) (fun y => g y / p)
    ha hb hδ (le_refl δ) hδsmall (div_nonneg hM hp.le) hMC
    (by rw [← Finset.sum_div, hftotal]) (by rw [← Finset.sum_div, hgtotal])
    (fun x => div_nonneg (Nat.cast_nonneg _) hp.le)
    (fun y => div_nonneg (Nat.cast_nonneg _) hp.le)
    (by
      intro x
      convert div_le_div_of_nonneg_right (hf x) hp.le using 1 <;> ring)
    (by
      intro y
      convert div_le_div_of_nonneg_right (hg y) hp.le using 1 <;> ring)
    hlarge
  let z (e : E) := p * q e
  have hz (e : E) : 0 ≤ z e ∧ z e ≤ p := by
    refine ⟨mul_nonneg hp.le (hq e).1, ?_⟩
    calc
      p * q e ≤ p * 1 := mul_le_mul_of_nonneg_left (hq e).2 hp.le
      _ = p := mul_one p
  have hzl (x : X) : (∑ e, if tail e = x then z e else 0) = f x := by
    have hh : (∑ e, if tail e = x then z e else 0) =
        p * (∑ e, if tail e = x then q e else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_zero, z]
    rw [hh, hleft, mul_div_cancel₀ _ hp.ne']
  have hzr (y : Y) : (∑ e, if head e = y then z e else 0) = g y := by
    have hh : (∑ e, if head e = y then z e else 0) =
        p * (∑ e, if head e = y then q e else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_zero, z]
    rw [hh, hright, mul_div_cancel₀ _ hp.ne']
  obtain ⟨ν, hν, he⟩ := bipartite_degree_rounding tail head f g z
    (fun e => ⟨(hz e).1, (hz e).2.trans hp1⟩)
    (by
      intro x
      convert hzl x using 1
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> rfl)
    (by
      intro y
      convert hzr y using 1
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> rfl)
  refine ⟨ν, ?_, fun e => (he e).le.trans (hz e).2⟩
  intro D hD
  obtain ⟨hl, hr⟩ := hν D hD
  constructor
  · intro x
    convert hl x using 1
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> rfl
  · intro y
    convert hr y using 1
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> rfl

end Oberwolfach
