module

public import Oberwolfach.FirstVortexEarlyDeletionRateBound
public import Oberwolfach.LongFirstVortexMatchingScaleActual

@[expose] public section
/-! The rates and early-deletion tolerance in the common selector satisfy
all rate and first-vortex scale hypotheses of the boundary construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_selector_actual_matching_rates
    (d K:ℕ) (θ lam ε δold eps ζ:ℝ) (n:ℕ)
    (hd:0<d) (hK:1≤K) (hθ:0<θ) (hθ1:θ≤1) (hlam:0<lam)
    (hε:0<ε) (hδ:0≤δold) (hδ1:δold≤1) (hlamδ:lam≤δold*ε/32)
    (hspacing:1/(d:ℝ)≤θ/1024) (heps:0<eps)
    (heps1:eps≤1) (hepsBudget:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hζ:ζ≤eps/8)
    (U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
    (Q:Vortex U G D β ε mm) (hmm:0<mm):
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    0<alpha ∧ 0<γ ∧ alpha≤lam/(10*d) ∧ γ≤lam/(10*d) ∧ γ≤eps ∧
    max alpha γ*(n:ℝ)≤(θ/4096)*(Q.extendedVertices 1).card ∧ ζ≤lam/3 :=by
  intro alpha γ
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hKR:0<(K:ℝ):=by exact_mod_cast (show 0<K by omega)
  have ha:0<alpha:=by dsimp [alpha]; positivity
  have hg:0<γ:=by dsimp [γ]; positivity
  have haRate:alpha≤lam/(10*d):=min_le_left _ _
  have hgRate:γ≤lam/(10*d):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hge:γ≤eps:=by have hh:γ≤eps/2:=min_le_left _ _; linarith
  have hscale:=long_first_vortex_matching_scale_actual d θ lam ε δold alpha γ n hd hθ hlam hε hδ hδ1 hlamδ hspacing haRate hgRate U G D mm β Q hmm
  have hdel:=first_vortex_early_deletion_rate_bound lam θ eps ζ K hlam.le hθ1 hK hepsBudget hζ
  exact ⟨ha,hg,haRate,hgRate,hge,hscale,hdel⟩
end Oberwolfach
