module

public import Oberwolfach.FirstVortexLateActiveLocalMatchingHierarchy

@[expose] public section
/-! The selector's exact definitions of the seed parameters are compatible
with an arbitrarily small later matching-rate bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_late_canonical_rates
    (d K:ℕ) (lam θ s:ℝ) (hd:0<d) (hK:0<K) (hlam:0<lam) (hθ:0<θ)
    (hs:0<s) (hlams:lam≤s):
    ∃eps a γ:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      a=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2)) ∧
      γ=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))) ∧
      0<a ∧ 0<γ ∧ a≤s ∧ γ≤s :=by
  have hdR:(1:ℝ)≤d:=by exact_mod_cast hd
  have hKR:(0:ℝ)<K:=by exact_mod_cast hK
  let eps:ℝ:=min 1 (lam*(θ/(100*(K:ℝ)^2))/6)
  let a:ℝ:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
  let γ:ℝ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
  have heps:0<eps:=by dsimp [eps];positivity
  have heps1:eps≤1:=min_le_left _ _
  have hepsrate:3*eps≤lam*(θ/(100*(K:ℝ)^2)):=by
    have hh:=min_le_right 1 (lam*(θ/(100*(K:ℝ)^2))/6)
    have hp:0≤lam*(θ/(100*(K:ℝ)^2)):=by positivity
    dsimp only [eps]
    nlinarith only [hh,hp]
  have ha:0<a:=by dsimp [a];positivity
  have hγ:0<γ:=by dsimp [γ];positivity
  have hdiv:lam/(10*(d:ℝ))≤lam:=by
    apply (div_le_iff₀ (show 0<10*(d:ℝ) by positivity)).2
    nlinarith
  have has:a≤s:=(min_le_left _ _).trans (hdiv.trans hlams)
  have hγs:γ≤s:=by
    have hh:γ≤lam/(10*(d:ℝ)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    exact hh.trans (hdiv.trans hlams)
  exact ⟨eps,a,γ,heps,heps1,hepsrate,rfl,rfl,ha,hγ,has,hγs⟩
end Oberwolfach
