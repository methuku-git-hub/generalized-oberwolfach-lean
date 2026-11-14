module

public import Oberwolfach.IndependentPatternSums
public import Oberwolfach.EdgeRetention

@[expose] public section

/-! Lower means for edge patterns, with every supplied edge probability
retained and only a common lower bound used in the estimate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pattern_survival_product_lower {E : Type*} [DecidableEq E]
    (R : Finset E) (ρ : E → ℝ) (p : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (hρ : ∀ e∈R,p≤ρ e) (q : ℕ) (hsize : R.card≤q) :
    p^q≤∏ e∈R,ρ e := by
  calc
    _ ≤ p^R.card := pow_le_pow_of_le_one hp hp1 hsize
    _ = ∏ _e∈R,p := (Finset.prod_const p).symm
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _=>hp) hρ


theorem pattern_survival_mean_lower {E I : Type*} [Fintype E] [DecidableEq E] [Fintype I]
    (μ : E → FiniteLaw Bool) (R : I → Finset E) (w : I → ℝ) (hw : ∀ i,0≤w i)
    (p : ℝ) (hp : 0≤p) (hp1 : p≤1) (q : ℕ)
    (hsize : ∀ i,(R i).card≤q) (hprob : ∀ i,∀ e∈R i,p≤(μ e).mass true) :
    p^q*(∑ i,w i)≤∑ i,w i*∏ e∈R i,(μ e).mass true := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hh := mul_le_mul_of_nonneg_left
    (pattern_survival_product_lower (R i) (fun e=>(μ e).mass true) p hp hp1 (hprob i) q (hsize i)) (hw i)
  simpa only [mul_comm] using hh

end Oberwolfach
