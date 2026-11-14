module

public import Oberwolfach.FirstVortexEarlyDeletionRateBound

@[expose] public section
/-! The actual matching selector's seed and deletion rates fit the later
inner-sum rate without constraining the earlier global loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_inner_sum_selector_rates
    (d K:ℕ) (s θ lam eps ζOrd:ℝ)
    (hd:0<d) (hK:0<K) (hs:0<s) (hθ:0<θ) (hθ1:θ≤1)
    (hlam:0<lam) (heps:0<eps) (hlams:lam≤s)
    (hepsRate:3*eps≤lam*(θ/(100*(K:ℝ)^2))) (hζ:ζOrd≤eps/8):
    let a:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    0<a ∧ a≤s ∧ 0<γ ∧ γ≤s ∧ ζOrd≤s :=by
  intro a γ
  have hdR:(1:ℝ)≤d:=by exact_mod_cast hd
  have hKR:(0:ℝ)<K:=by exact_mod_cast hK
  have ha:0<a:=by dsimp [a];positivity
  have hg:0<γ:=by dsimp [γ];positivity
  have hdiv:lam/(10*(d:ℝ))≤lam:=by
    apply (div_le_iff₀ (show 0<10*(d:ℝ) by positivity)).2
    nlinarith
  have has:a≤s:=(min_le_left _ _).trans (hdiv.trans hlams)
  have hgs:γ≤s:=by
    have hh:γ≤lam/(10*(d:ℝ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact hh.trans (hdiv.trans hlams)
  have hdel:=first_vortex_early_deletion_rate_bound lam θ eps ζOrd K hlam.le hθ1 (by omega) hepsRate hζ
  have hds:ζOrd≤s:=by linarith
  exact ⟨ha,has,hg,hgs,hds⟩
end Oberwolfach
