module

public import Oberwolfach.NearUniformRandomDemands

@[expose] public section

/-! Interval bounds imply the quantitative hypotheses for random demands. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem interval_random_demands {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (tail head : E → V) (f g : V → ℕ) (a b δ h p : ℝ)
    (hn : 0 < Fintype.card V) (ha : 0 < a) (hp : 0 < p) (hp1 : p ≤ 1)
    (hδ : 0 ≤ δ) (hδsmall : δ < 1 / 4)
    (hrelative : b ≤ (1 + δ) * a)
    (hcapacity : b ≤ p * h * Fintype.card V / 2)
    (hf : ∀ x, a ≤ (f x : ℝ) ∧ (f x : ℝ) ≤ b)
    (hg : ∀ y, a ≤ (g y : ℝ) ∧ (g y : ℝ) ≤ b)
    (htotal : ∑ x, f x = ∑ y, g y)
    (hlarge : ∀ (S T : Finset V),
      1 - 2 * δ < (S.card : ℝ) / Fintype.card V + (T.card : ℝ) / Fintype.card V →
      h * Fintype.card V * Fintype.card V *
        min ((S.card : ℝ) / Fintype.card V) ((T.card : ℝ) / Fintype.card V) ≤
      ((Finset.univ.filter (fun e => tail e ∈ S ∧ head e ∈ T)).card : ℝ)) :
    ∃ ν : FiniteLaw (E → Bool),
      (∀ D, 0 < ν.mass D →
        (∀ x, (∑ e, if tail e = x ∧ D e = true then (1 : ℕ) else 0) = f x) ∧
        (∀ y, (∑ e, if head e = y ∧ D e = true then (1 : ℕ) else 0) = g y)) ∧
      (∀ e, ν.probability (fun D => D e = true) ≤ p) := by
  let M : ℝ := ∑ x, (f x : ℝ)
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hM : 0 ≤ M := Finset.sum_nonneg (fun x _ => Nat.cast_nonneg _)
  have hMlo : Fintype.card V * a ≤ M := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun x _ => (hf x).1)
  have hMhi : M ≤ Fintype.card V * b := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (s := Finset.univ) (fun x _ => (hf x).2)
  have hMC : M / p ≤ h * Fintype.card V * Fintype.card V / 2 := by
    apply (div_le_iff₀ hp).mpr
    calc
      M ≤ Fintype.card V * b := hMhi
      _ ≤ Fintype.card V * (p * h * Fintype.card V / 2) :=
        mul_le_mul_of_nonneg_left hcapacity hn'.le
      _ = _ := by ring
  have hbound (u : ℝ) (hu : u ≤ b) : u ≤ (1 + δ) * M / Fintype.card V := by
    apply (le_div_iff₀ hn').mpr
    calc
      u * Fintype.card V ≤ b * Fintype.card V := mul_le_mul_of_nonneg_right hu hn'.le
      _ ≤ ((1 + δ) * a) * Fintype.card V := mul_le_mul_of_nonneg_right hrelative hn'.le
      _ = (1 + δ) * (Fintype.card V * a) := by ring
      _ ≤ (1 + δ) * M := mul_le_mul_of_nonneg_left hMlo (by linarith)
  apply nearUniform_random_demands tail head f g δ M h p hp hp1 hn hn hδ hδsmall hM hMC
    rfl _ (fun x => hbound _ (hf x).2) (fun y => hbound _ (hg y).2) hlarge
  dsimp [M]
  exact_mod_cast htotal.symm

end Oberwolfach
