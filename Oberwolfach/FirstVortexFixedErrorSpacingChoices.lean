module

public import Oberwolfach.FirstVortexMatchingOrderedChoices

@[expose] public section
/-! With the matching error already fixed, only the incidence tolerances
need depend on the spacing parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_fixed_error_spacing_choices
    (K:ℕ) (lam θ ε ρ eps:ℝ) (hK:0<K)
    (hlam:0<lam) (hθ:0<θ) (hε:0<ε) (hρ:0<ρ) (heps:0<eps):
    ∀d:ℕ,0<d→∃a γ:ℝ,
      0<a ∧ a≤lam/(10*d) ∧ a≤θ/(200*(K:ℝ)^2) ∧
      0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
      ∀(n A:ℕ), ε*n/2≤A→max a γ*n≤ρ*A:=by
  intro d hd
  let a:ℝ:=min (lam/(10*d)) (min (θ/(200*(K:ℝ)^2)) (ρ*ε/2))
  let γ:ℝ:=min (eps/2) (min (1/2) (min (lam/(10*d)) (ρ*ε/2)))
  have hdR:(0:ℝ)<d:=by exact_mod_cast hd
  have hd1:(1:ℝ)≤d:=by exact_mod_cast hd
  have hKR:(0:ℝ)<K:=by exact_mod_cast hK
  have ha:0<a:=by dsimp [a];positivity
  have haD:a≤lam/(10*d):=min_le_left _ _
  have haθ:a≤θ/(200*(K:ℝ)^2):=(min_le_right _ _).trans (min_le_left _ _)
  have haScale:a≤ρ*ε/2:=(min_le_right _ _).trans (min_le_right _ _)
  have hγ:0<γ:=by dsimp [γ];positivity
  have hγeps2:γ≤eps/2:=min_le_left _ _
  have hγeps:γ≤eps:=by linarith
  have hγhalf:γ≤1/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hγD:γ≤lam/(10*d):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγlam:γ≤lam/10:=by
    have hh:=mul_nonneg hlam.le (sub_nonneg.mpr hd1)
    apply le_trans hγD
    apply (div_le_iff₀ (show 0<10*(d:ℝ) by positivity)).2
    nlinarith only [hh]
  have hγScale:γ≤ρ*ε/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨a,γ,ha,haD,haθ,hγ,hγeps,hγeps2,hγhalf,hγD,hγlam,?_⟩
  intro n A hA
  have hmax:max a γ≤ρ*ε/2:=max_le haScale hγScale
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hm:=mul_le_mul_of_nonneg_right hmax hn
  have hρA:=mul_le_mul_of_nonneg_left hA hρ.le
  nlinarith only [hm,hρA]
end Oberwolfach
