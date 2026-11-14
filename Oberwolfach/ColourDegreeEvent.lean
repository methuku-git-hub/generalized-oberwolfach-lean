module

public import Oberwolfach.ColourDegrees
public import Oberwolfach.OrientationMargins

@[expose] public section

/-! One event for both directed colour degrees and the colour degrees
inside a fixed protected graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
universe u
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sampledColourDegrees_common_event
    {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ} (G Z : SimpleGraph V)
    (ρ : Fin k → ℝ) (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1)
    {t : ℝ} (ht : 0 ≤ t) :
    1 - 6 * k * Fintype.card V * Real.exp (-2 * t ^ 2 / Fintype.card V) ≤
      (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
        (fun σ => ∀ a x,
          |((∑ y, sampledColourOrientation G σ a x y : ℕ) : ℝ) - ρ a / 2 * G.degree x| < t ∧
          |((∑ y, sampledColourOrientation G σ a y x : ℕ) : ℝ) - ρ a / 2 * G.degree x| < t ∧
          |(sampledColourDegree Z (fun e => (σ e).1) a x : ℝ) - ρ a * Z.degree x| < t) := by
  let J := Fin k × (V × Fin 3)
  let X (j : J) (σ : Sym2 V → Fin k × Bool) : ℝ :=
    match j.2.2 with
    | 0 => ((∑ y, sampledColourOrientation G σ j.1 j.2.1 y : ℕ) : ℝ) - ρ j.1 / 2 * G.degree j.2.1
    | 1 => ((∑ y, sampledColourOrientation G σ j.1 y j.2.1 : ℕ) : ℝ) - ρ j.1 / 2 * G.degree j.2.1
    | _ => (sampledColourDegree Z (fun e => (σ e).1) j.1 j.2.1 : ℝ) - ρ j.1 * Z.degree j.2.1
  let b := 2 * Real.exp (-2 * t ^ 2 / Fintype.card V)
  have hbad (j : J) :
      (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
        (fun σ => t ≤ |X j σ|) ≤ b := by
    obtain ⟨a, x, j⟩ := j
    fin_cases j
    · exact sampledColourOrientation_degree_tail G ρ hρ htotal a x ht
    · exact sampledColourOrientation_indegree_tail G ρ hρ htotal a x ht
    · exact sampledColourDegree_joint_tail Z ρ hρ htotal a x ht
  have hh := finiteLaw_common_event_lower
    (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal))
    Finset.univ (fun j σ => t ≤ |X j σ|) (fun _ => b) (fun j _ => hbad j)
  have hsum : (∑ _ : J, b) = 6 * k * Fintype.card V * Real.exp (-2 * t ^ 2 / Fintype.card V) := by
    simp only [Finset.sum_const, Finset.card_univ, J, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_mul, Nat.cast_ofNat, nsmul_eq_mul, b]
    ring
  rw [hsum] at hh
  apply hh.trans
  apply finiteLaw_probability_mono
  intro σ hσ a x
  exact ⟨not_le.mp (hσ (a, x, 0) (Finset.mem_univ _)),
    not_le.mp (hσ (a, x, 1) (Finset.mem_univ _)),
    not_le.mp (hσ (a, x, 2) (Finset.mem_univ _))⟩

theorem sampledColourDegrees_highProbability (k p : ℕ) :
    ∃ N₀ : ℕ, ∀ (V : Type u) [Fintype V] [LinearOrder V],
      let n := Fintype.card V
      N₀ ≤ n → ∀ (G Z : SimpleGraph V) (ρ : Fin k → ℝ)
        (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1),
      1 - 1 / (n : ℝ) ^ p ≤
        (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
          (fun σ => ∀ a x,
            |((∑ y, sampledColourOrientation G σ a x y : ℕ) : ℝ) - ρ a / 2 * G.degree x| <
              (n : ℝ) ^ (3 / 5 : ℝ) ∧
            |((∑ y, sampledColourOrientation G σ a y x : ℕ) : ℝ) - ρ a / 2 * G.degree x| <
              (n : ℝ) ^ (3 / 5 : ℝ) ∧
            |(sampledColourDegree Z (fun e => (σ e).1) a x : ℝ) - ρ a * Z.degree x| <
              (n : ℝ) ^ (3 / 5 : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_stretchedExp_le_inv_pow (6 * k) 1
    (c := 2) (p := 1 / 5) (by norm_num) (by norm_num) p
  refine ⟨max N 1, fun V _ _ => ?_⟩
  intro n hn G Z ρ hρ htotal
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := sampledColourDegrees_common_event G Z ρ hρ htotal
    (t := (n : ℝ) ^ (3 / 5 : ℝ)) (by positivity)
  change 1 - 6 * k * n * Real.exp (-2 * ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / n) ≤ _ at hh
  rw [threeFifths_tail_exponent hnpos] at hh
  have hb := hN n (le_trans (le_max_left _ _) hn)
  simp only [Real.rpow_one] at hb
  exact (sub_le_sub_left hb 1).trans hh

end Oberwolfach
