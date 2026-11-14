module

public import Oberwolfach.OrdinaryInducedParentThreshold
public import Oberwolfach.OrdinaryInducedRimCutProbability

@[expose] public section
/-! The induced rim event follows from the parent-density hypothesis on the
    actual inner set, under the original ambient sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_induced_rim_cut_from_parent_density
    (α pstar : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/2) (hpstar : 0 < pstar) (q₀ : ℕ) :
    ∃ N : ℕ, ∀ (V U Γ Color : Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P : SimpleGraph V) (I : Finset V), N ≤ I.card →
    ∀ density : ℝ, cycleThreshold 3 + α ≤ density →
      (∀ v, density * I.card ≤ ((I ∩ P.neighborFinset v).card : ℝ)) →
    ∀ (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1), pstar ≤ p →
    ∀ d : ℕ, ∀ hd : 2 ≤ d,
    ∀ (q : U → Γ → ℝ) (hq : ∀ u g, 0 ≤ q u g) (hQ : ∀ u, ∑ g, q u g ≤ 1/8)
      (s : U → Color → ℝ) (hs : ∀ u j, 0 ≤ s u j)
      (hS : ∀ u, ∑ j, s u j ≤ intervalUncoveredProbability d (∑ g, q u g)),
    1 - 1 / (I.card : ℝ)^q₀ ≤
      ((FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V => p) (fun _ => hp) (fun _ => hp1) d hd q hq hQ s hs hS)).prod
        (FiniteLaw.pi (fun _ : Sym2 V => FiniteLaw.fairCoin))).probability (fun z =>
      OrdinaryInducedRimCutEvent I (sampledOrientation (rawWheelGraph P z.1) z.2) α pstar) := by
  obtain ⟨N, hN⟩ := ordinary_induced_rim_cut_high_probability α pstar hα hα1 hpstar q₀
  refine ⟨N, ?_⟩
  intro V U Γ Color _ _ _ _ _ _ P I hn density hthreshold hmin p hp hp1 hplo d hd q hq hQ s hs hS
  have hparent := ordinary_induced_parent_threshold_from_density P I density α hthreshold hmin
  have hhalf : (1/2 : ℝ) ≤ cycleThreshold 3 := cycleThreshold_half_le (by omega)
  have hcoef : (1/2 : ℝ) + α ≤ cycleThreshold 3 + α := by linarith
  have hdegree : ∀ v : I, (1/2 + α) * I.card ≤ ((P.induce (I : Set V)).degree v : ℝ) := by
    intro v
    exact (mul_le_mul_of_nonneg_right hcoef (by positivity : (0 : ℝ) ≤ I.card)).trans (hparent v)
  exact hN V U Γ Color P I hn hdegree p hp hp1 hplo d hd q hq hQ s hs hS
end Oberwolfach
