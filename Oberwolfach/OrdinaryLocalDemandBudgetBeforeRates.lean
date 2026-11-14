module

public import Oberwolfach.OrdinaryPlacementRatesProportionalBeforeSpacing

@[expose] public section
/-! A protected-set contraction selected from the fixed proportionality
constant controls the later local matching and exceptional-colour demand. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_local_demand_budget_before_rates
    (c cap:ℝ) (hc:0<c) (hcap:0<cap):
    ∃ε:ℝ,0<ε ∧ ε ≤ cap ∧ ∀(n θ b inner a γ q t edit aux del bad:ℝ),
      0 ≤ n → 0 ≤ θ → 0 ≤ inner → c*θ ≤ b → inner ≤ ε*n →
      a ≤ b/16 → γ ≤ θ → q ≤ 3*θ → t ≤ θ*inner →
      edit ≤ b*n/16 → aux ≤ b*n/16 → del ≤ b*n/16 → bad ≤ b*n/16 →
      edit+max (a*n) (γ*inner)+q*inner+3*t+aux+del+bad ≤ b*n :=by
  let ε:ℝ:=min (c/100) cap
  have hε:0<ε:=by dsimp [ε];positivity
  have hεcap:ε ≤ cap:=min_le_right _ _
  refine ⟨ε,hε,hεcap,?_⟩
  intro n θ b inner a γ q t edit aux del bad hn hθ hi hb hinner ha hγ hq ht he haux hdel hbad
  have hθinner:θ*inner ≤ b*n/100:=by
    have hεn:=mul_le_mul_of_nonneg_right (min_le_left (c/100) cap) hn
    have hinner':inner ≤ (c/100)*n:=hinner.trans hεn
    have h1:=mul_le_mul_of_nonneg_left hinner' hθ
    have h2:=mul_le_mul_of_nonneg_right hb hn
    nlinarith [h1,h2]
  have hfirst:a*n ≤ b*n/16:=by
    have h:=mul_le_mul_of_nonneg_right ha hn
    nlinarith
  have hsecond:γ*inner ≤ b*n/100:=by
    have h:=mul_le_mul_of_nonneg_right hγ hi
    linarith
  have hbn:0 ≤ b*n:=by
    have hb0:0 ≤ b:=le_trans (mul_nonneg (le_of_lt hc) hθ) hb
    positivity
  have hmax:max (a*n) (γ*inner) ≤ b*n/16:=by
    apply max_le hfirst
    nlinarith
  have hqinner:q*inner ≤ 3*(b*n/100):=by
    have h:=mul_le_mul_of_nonneg_right hq hi
    nlinarith
  have ht':t ≤ b*n/100:=ht.trans hθinner
  linarith
end Oberwolfach
