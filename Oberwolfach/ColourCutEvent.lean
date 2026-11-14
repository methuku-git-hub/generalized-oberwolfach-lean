module

public import Oberwolfach.RandomColourCuts
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! One simultaneous directed-colour cut event, with its asymptotic
probability proved uniformly over all host graphs and colour profiles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
universe u
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampledColourCut_quadratic_event_pow (k : ℕ) {q : ℝ} (hq : 0 < q) (p : ℕ) :
    ∃ N₀ : ℕ, ∀ (V : Type u) [Fintype V] [LinearOrder V],
      let n := Fintype.card V
      N₀ ≤ n → ∀ (G : SimpleGraph V) (ρ : Fin k → ℝ)
        (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1),
      1 - 1 / (n : ℝ) ^ p ≤
        (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
          (fun σ => ∀ a S T,
            |((∑ x ∈ S, ∑ y ∈ T, sampledColourOrientation G σ a x y : ℕ) : ℝ) -
              ρ a / 2 * graphCut G S T| < q * (n : ℝ) ^ 2) := by
  obtain ⟨N, hN⟩ := eventually_allCuts_failure_small
    (C := 2 * k) (c := q ^ 2 / 2) (by positivity) (by positivity) p
  refine ⟨max N 1, fun V _ _ => ?_⟩
  intro n hn G ρ hρ htotal
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hh := sampledColourCut_all_cuts G hnpos ρ hρ htotal
    (fun _ => q * (n : ℝ) ^ 2) (fun _ => by positivity)
  have heq : -(q * (n : ℝ) ^ 2) ^ 2 / (2 * (n : ℝ) ^ 2) = -(q ^ 2 / 2) * (n : ℝ) ^ 2 := by
    field_simp
  change 1 - (4 : ℝ) ^ n *
      (∑ _a : Fin k, 2 * Real.exp (-(q * (n : ℝ) ^ 2) ^ 2 / (2 * (n : ℝ) ^ 2))) ≤ _ at hh
  simp only [heq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hs := hN n (le_trans (le_max_left _ _) hn)
  have heq' : (4 : ℝ) ^ n * (k * (2 * Real.exp (-(q ^ 2 / 2) * (n : ℝ) ^ 2))) =
      2 * k * (4 : ℝ) ^ n * Real.exp (-(q ^ 2 / 2) * (n : ℝ) ^ 2) := by ring
  rw [heq'] at hh
  exact (sub_le_sub_left hs 1).trans hh


theorem sampledColourCut_quadratic_event (k : ℕ) {q : ℝ} (hq : 0 < q) :
    ∃ N₀ : ℕ, ∀ (V : Type u) [Fintype V] [LinearOrder V],
      let n := Fintype.card V
      N₀ ≤ n → ∀ (G : SimpleGraph V) (ρ : Fin k → ℝ)
        (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1),
      1 - 1 / (n : ℝ) ^ 10 ≤
        (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
          (fun σ => ∀ a S T,
            |((∑ x ∈ S, ∑ y ∈ T, sampledColourOrientation G σ a x y : ℕ) : ℝ) -
              ρ a / 2 * graphCut G S T| < q * (n : ℝ) ^ 2) :=
  sampledColourCut_quadratic_event_pow k hq 10

end Oberwolfach
