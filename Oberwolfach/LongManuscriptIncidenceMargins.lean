module

public import Oberwolfach.LongRawMatchingIncidenceBounds

@[expose] public section
/-! The displayed matching parameters give the manuscript's absolute
auxiliary, spoke and physical residual margins. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem long_manuscript_matching_incidence_margins
    (K d n:ℕ) (hK:0<K) (hd:2≤d) (θ lam:ℝ) (hθ:0<θ) (hlam:0<lam):
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))
    max alpha (4*γ)≤lam ∧ max alpha γ≤lam/4 ∧
    ∀δ:ℝ,δ≤(lam/2)*n→max alpha γ*n+δ≤lam*n :=by
  intro alpha γ
  have hdpos:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hd2:(2:ℝ)≤d:=by exact_mod_cast hd
  have hfrac:lam/(10*(d:ℝ))≤lam/20:=by
    apply (div_le_iff₀ (by positivity : 0<10*(d:ℝ))).2
    nlinarith
  have ha:alpha≤lam/20:= (min_le_left _ _).trans hfrac
  have hg:γ≤lam/20:= (min_le_right _ _).trans ((min_le_left _ _).trans hfrac)
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  have haux:max alpha (4*γ)≤lam:=by apply max_le <;> linarith
  have hspoke:max alpha γ≤lam/4:=by apply max_le <;> linarith
  refine ⟨haux,hspoke,?_⟩
  intro δ hδ
  have hm:=mul_le_mul_of_nonneg_right hspoke hn
  nlinarith
end Oberwolfach
