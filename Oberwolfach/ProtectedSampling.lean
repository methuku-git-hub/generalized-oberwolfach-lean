module

public import Oberwolfach.BalancedOrientation
public import Oberwolfach.ColourDegreeEvent
public import Oberwolfach.ColourCutEvent

@[expose] public section

/-! One event containing the raw degree and cut estimates and every later
balanced orientation required by the protected partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
universe u
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_inter_lower {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (A B : Ω → Prop) :
    μ.probability A + μ.probability B - 1 ≤ μ.probability (fun ω => A ω ∧ B ω) := by
  rw [sub_le_iff_le_add, ← μ.total]
  unfold FiniteLaw.probability
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases ha : A ω <;> by_cases hb : B ω <;> simp [ha, hb, μ.nonneg ω]

structure ProtectedSampleGood {V : Type*} [Fintype V] [LinearOrder V] {k : ℕ}
    (G Z : SimpleGraph V) (ρ : Fin k → ℝ) (α q : ℝ)
    (σ : Sym2 V → Fin k × Bool) : Prop where
  degrees : ∀ a x,
    |((∑ y, sampledColourOrientation G σ a x y : ℕ) : ℝ) - ρ a / 2 * G.degree x| <
      (Fintype.card V : ℝ) ^ (3 / 5 : ℝ) ∧
    |((∑ y, sampledColourOrientation G σ a y x : ℕ) : ℝ) - ρ a / 2 * G.degree x| <
      (Fintype.card V : ℝ) ^ (3 / 5 : ℝ) ∧
    |(sampledColourDegree Z (fun e => (σ e).1) a x : ℝ) - ρ a * Z.degree x| <
      (Fintype.card V : ℝ) ^ (3 / 5 : ℝ)
  cuts : ∀ a S T,
    |((∑ x ∈ S, ∑ y ∈ T, sampledColourOrientation G σ a x y : ℕ) : ℝ) -
      ρ a / 2 * graphCut G S T| < q * (Fintype.card V : ℝ) ^ 2
  balance : ∀ F : SimpleGraph V, (∀ v, (F.degree v : ℝ) ≤ α * Fintype.card V / 100) →
    ∃ M : V → V → ℕ,
      (∀ x y, M x y + M y x = if G.Adj x y then 1 else 0) ∧
      (∀ v, (∑ w, M v w) = G.degree v / 2 ∧ (∑ w, M w v) = G.degree v / 2) ∧
      (∀ x y, M x y ≠ sampledOrientation G (fun e => (σ e).2) x y ∨
        M y x ≠ sampledOrientation G (fun e => (σ e).2) y x → ¬ F.Adj x y) ∧
      ∀ x, ((Finset.univ.filter (fun y => M x y ≠ sampledOrientation G (fun e => (σ e).2) x y ∨
        M y x ≠ sampledOrientation G (fun e => (σ e).2) y x)).card : ℝ) ≤
          4 * (Fintype.card V : ℝ) ^ (4 / 5 : ℝ)

theorem protectedSample_highProbability (k p : ℕ) {α q : ℝ} (hα : 0 < α) (hq : 0 < q) :
    ∃ N₀ : ℕ, ∀ (V : Type u) [Fintype V] [LinearOrder V],
      let n := Fintype.card V
      N₀ ≤ n → ∀ (G Z : SimpleGraph V) (ρ : Fin k → ℝ)
        (hρ : ∀ a, 0 ≤ ρ a) (htotal : ∑ a, ρ a = 1),
      (∀ v, Even (G.degree v)) →
      (∀ v, (1 / 2 + α) * n ≤ (G.degree v : ℝ)) →
      1 - 1 / (n : ℝ) ^ p ≤
        (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)).probability
          (ProtectedSampleGood G Z ρ α q) := by
  obtain ⟨N₁, h₁⟩ := balancedOrientation_highProbability_pow hα (p + 2)
  obtain ⟨N₂, h₂⟩ := sampledColourDegrees_highProbability k (p + 2)
  obtain ⟨N₃, h₃⟩ := sampledColourCut_quadratic_event_pow k hq (p + 2)
  refine ⟨max 2 (max N₁ (max N₂ N₃)), fun V _ _ => ?_⟩
  intro n hn G Z ρ hρ htotal heven hmin
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hnpos : (0 : ℝ) < n := by linarith
  let μ := FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.categoricalDirection ρ hρ htotal)
  have hd := h₂ V (by omega) G Z ρ hρ htotal
  have hc := h₃ V (by omega) G ρ hρ htotal
  have ho := h₁ V (by omega) G heven hmin
  let O := fun σ : Sym2 V → Bool => ∀ F : SimpleGraph V,
    (∀ v, (F.degree v : ℝ) ≤ α * n / 100) →
    ∃ M : V → V → ℕ,
      (∀ x y, M x y + M y x = if G.Adj x y then 1 else 0) ∧
      (∀ v, (∑ w, M v w) = G.degree v / 2 ∧ (∑ w, M w v) = G.degree v / 2) ∧
      (∀ x y, M x y ≠ sampledOrientation G σ x y ∨ M y x ≠ sampledOrientation G σ y x → ¬ F.Adj x y) ∧
      ∀ x, ((Finset.univ.filter (fun y => M x y ≠ sampledOrientation G σ x y ∨
        M y x ≠ sampledOrientation G σ y x)).card : ℝ) ≤ 4 * (n : ℝ) ^ (4 / 5 : ℝ)
  have ho' : 1 - 1 / (n : ℝ) ^ (p + 2) ≤ μ.probability (fun σ => O (fun e => (σ e).2)) := by
    rw [categoricalDirection_direction_probability ρ hρ htotal O]
    exact ho
  let A := fun σ => ∀ a x,
    |((∑ y, sampledColourOrientation G σ a x y : ℕ) : ℝ) - ρ a / 2 * G.degree x| <
      (n : ℝ) ^ (3 / 5 : ℝ) ∧
    |((∑ y, sampledColourOrientation G σ a y x : ℕ) : ℝ) - ρ a / 2 * G.degree x| <
      (n : ℝ) ^ (3 / 5 : ℝ) ∧
    |(sampledColourDegree Z (fun e => (σ e).1) a x : ℝ) - ρ a * Z.degree x| < (n : ℝ) ^ (3 / 5 : ℝ)
  let C := fun σ => ∀ a S T,
    |((∑ x ∈ S, ∑ y ∈ T, sampledColourOrientation G σ a x y : ℕ) : ℝ) -
      ρ a / 2 * graphCut G S T| < q * (n : ℝ) ^ 2
  have hdc := finiteLaw_inter_lower μ A C
  have hall := finiteLaw_inter_lower μ (fun σ => A σ ∧ C σ) (fun σ => O (fun e => (σ e).2))
  have hmono : μ.probability (fun σ => (A σ ∧ C σ) ∧ O (fun e => (σ e).2)) ≤
      μ.probability (ProtectedSampleGood G Z ρ α q) := by
    apply finiteLaw_probability_mono
    intro σ hσ
    exact ⟨hσ.1.1, hσ.1.2, hσ.2⟩
  have hpow : 3 / (n : ℝ) ^ (p + 2) ≤ 1 / (n : ℝ) ^ p := by
    apply (div_le_div_iff₀ (pow_pos hnpos _) (pow_pos hnpos _)).mpr
    rw [pow_add]
    have hs : (3 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    simpa only [one_mul, mul_one, mul_comm] using mul_le_mul_of_nonneg_left hs (pow_nonneg hnpos.le p)
  change 1 - 1 / (n : ℝ) ^ (p + 2) ≤ μ.probability A at hd
  change 1 - 1 / (n : ℝ) ^ (p + 2) ≤ μ.probability C at hc
  change _ ≤ μ.probability _
  have hpow' : 3 * (1 / (n : ℝ) ^ (p + 2)) ≤ 1 / (n : ℝ) ^ p := by
    simpa only [div_eq_mul_inv, one_mul] using hpow
  linarith only [hd, hc, ho', hdc, hall, hmono, hpow']

end Oberwolfach
