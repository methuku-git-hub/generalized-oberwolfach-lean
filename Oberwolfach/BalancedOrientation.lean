module

public import Oberwolfach.OrientationMargins

@[expose] public section

/-! The manuscript's high-probability balanced-orientation claim, with one
sampling event for every later forbidden graph and an order threshold
chosen solely from alpha. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
universe u
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem orientationMatrix_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V) (M : V → V → ℕ)
    (hphysical : ∀ x y, M x y + M y x = if G.Adj x y then 1 else 0) (x : V) :
    (∑ y, M x y) + (∑ y, M y x) = G.degree x := by
  rw [← Finset.sum_add_distrib]
  simp only [hphysical]
  rw [← Finset.card_filter]
  congr 1
  ext y
  simp

/-- An exact statement of the balanced-orientation claim used by the
protected partition. The only hypotheses on the graph are even degrees
and its minimum-degree bound. All concentration, routing, rounding and
asymptotic choices are discharged. -/
theorem balancedOrientation_highProbability_pow {α : ℝ} (hα : 0 < α) (q : ℕ) :
    ∃ N₀ : ℕ, ∀ (V : Type u) [Fintype V] [LinearOrder V],
      let n := Fintype.card V
      N₀ ≤ n → ∀ G : SimpleGraph V,
      (∀ v, Even (G.degree v)) →
      (∀ v, (1 / 2 + α) * n ≤ (G.degree v : ℝ)) →
      1 - 1 / (n : ℝ) ^ q ≤
        (FiniteLaw.pi (fun _ : Sym2 (V) => FiniteLaw.fairCoin)).probability (fun σ =>
          ∀ F : SimpleGraph (V), (∀ v, (F.degree v : ℝ) ≤ α * n / 100) →
          ∃ M : V → V → ℕ,
            (∀ x y, M x y + M y x = if G.Adj x y then 1 else 0) ∧
            (∀ v, (∑ w, M v w) = G.degree v / 2 ∧ (∑ w, M w v) = G.degree v / 2) ∧
            (∀ x y, M x y ≠ sampledOrientation G σ x y ∨
              M y x ≠ sampledOrientation G σ y x → ¬ F.Adj x y) ∧
            ∀ x, ((Finset.univ.filter (fun y => M x y ≠ sampledOrientation G σ x y ∨
              M y x ≠ sampledOrientation G σ y x)).card : ℝ) ≤ 4 * (n : ℝ) ^ (4 / 5 : ℝ)) := by
  obtain ⟨N₁, h₁⟩ := eventually_orientation_numeric hα
  obtain ⟨N₂, h₂⟩ := eventually_orientation_failure_small_pow hα q
  refine ⟨max N₁ N₂, fun V _ _ => ?_⟩
  intro n hn G heven hmin
  obtain ⟨hnpos, hL, hmargin, hchange⟩ := h₁ n (le_trans (le_max_left _ _) hn)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hfailure := h₂ n (le_trans (le_max_right _ _) hn)
  let d (v : V) := G.degree v / 2
  have hd (v : V) : 2 * d v = G.degree v := by
    obtain ⟨k, hk⟩ := heven v
    dsimp [d]
    omega
  have hc := commonNeighbours_of_minDegree G hmin
  have hcommon (x y : V) (_hxy : x ≠ y) :
      8 * (α / 4) * Fintype.card (V) ≤
        ((G.neighborFinset x ∩ G.neighborFinset y).card : ℝ) := by
    have hh := hc x y
    linarith
  have hdegree (v : V) : 0 < G.degree v := by
    have hpos : (0 : ℝ) < (1 / 2 + α) * n := by positivity
    have hh := hpos.trans_le (hmin v)
    exact_mod_cast hh
  have hprob := sampledOrientation_balancing_event G G le_rfl d hd
    (Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ))) hL hnpos
    (a := (n : ℝ) ^ (3 / 5 : ℝ)) (f := α * n / 100) (β := α / 4)
    (by positivity) (by positivity) (by positivity) hcommon
    hmargin
  have hsum := orientation_failure_sum_bound G G hdegree
    (a := (n : ℝ) ^ (3 / 5 : ℝ)) (α := α) (fun x y _ => hc x y)
  change _ ≤ 2 * n * Real.exp (-2 * ((n : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / n) +
    2 * (n : ℝ) ^ 2 * Real.exp (-α * n / 32) at hsum
  rw [threeFifths_tail_exponent hnreal] at hsum
  have hbase : 1 - 1 / (n : ℝ) ^ q ≤
      (FiniteLaw.pi (fun _ : Sym2 (V) => FiniteLaw.fairCoin)).probability (fun σ =>
        ∀ F : SimpleGraph (V), (∀ v, (F.degree v : ℝ) ≤ α * n / 100) →
        ∃ M : V → V → ℕ,
          (∀ x y, M x y + M y x = if G.Adj x y then 1 else 0) ∧
          (∀ v, ∑ w, M v w = d v) ∧
          (∀ x y, M x y ≠ sampledOrientation G σ x y ∨ M y x ≠ sampledOrientation G σ y x →
            G.Adj x y ∧ ¬ F.Adj x y) ∧
          ∀ x, ((Finset.univ.filter (fun y => M x y ≠ sampledOrientation G σ x y ∨
            M y x ≠ sampledOrientation G σ y x)).card : ℝ) ≤
              (n : ℝ) ^ (3 / 5 : ℝ) + 2 * Nat.ceil ((n : ℝ) ^ (4 / 5 : ℝ))) := by
    apply le_trans ?_ hprob
    linarith [hsum, hfailure]
  apply hbase.trans
  apply finiteLaw_probability_mono
  intro σ hσ F hF
  obtain ⟨M, hphys, hout, havoid, hsize⟩ := hσ F hF
  refine ⟨M, hphys, ?_, fun x y h => (havoid x y h).2,
    fun x => (hsize x).trans hchange⟩
  intro v
  have hh := orientationMatrix_degree G M hphys v
  rw [hout v] at hh
  have hdv := hd v
  exact ⟨hout v, by dsimp [d] at *; omega⟩


theorem balancedOrientation_highProbability {α : ℝ} (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ (V : Type u) [Fintype V] [LinearOrder V],
      let n := Fintype.card V
      N₀ ≤ n → ∀ G : SimpleGraph V,
      (∀ v, Even (G.degree v)) →
      (∀ v, (1 / 2 + α) * n ≤ (G.degree v : ℝ)) →
      1 - 1 / (n : ℝ) ^ 10 ≤
        (FiniteLaw.pi (fun _ : Sym2 (V) => FiniteLaw.fairCoin)).probability (fun σ =>
          ∀ F : SimpleGraph (V), (∀ v, (F.degree v : ℝ) ≤ α * n / 100) →
          ∃ M : V → V → ℕ,
            (∀ x y, M x y + M y x = if G.Adj x y then 1 else 0) ∧
            (∀ v, (∑ w, M v w) = G.degree v / 2 ∧ (∑ w, M w v) = G.degree v / 2) ∧
            (∀ x y, M x y ≠ sampledOrientation G σ x y ∨
              M y x ≠ sampledOrientation G σ y x → ¬ F.Adj x y) ∧
            ∀ x, ((Finset.univ.filter (fun y => M x y ≠ sampledOrientation G σ x y ∨
              M y x ≠ sampledOrientation G σ y x)).card : ℝ) ≤ 4 * (n : ℝ) ^ (4 / 5 : ℝ)) :=
  balancedOrientation_highProbability_pow hα 10

end Oberwolfach
