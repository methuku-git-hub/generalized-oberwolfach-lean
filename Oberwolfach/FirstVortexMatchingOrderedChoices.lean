module

public import Oberwolfach.FirstVortexMatchingErrorBudget

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_ordered_choices
    (d K:ℕ) (lam θ ε ρ:ℝ) (hd:0<d) (hK:0<K)
    (hlam:0<lam) (hθ:0<θ) (hε:0<ε) (hρ:0<ρ):
    ∃eps a γ:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      0<a ∧ a≤lam/(10*d) ∧ a≤θ/(200*(K:ℝ)^2) ∧
      0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
      ∀(n A:ℕ), ε*n/2≤A→max a γ*n≤ρ*A:=by
  let eps:ℝ:=min 1 (lam*(θ/(100*(K:ℝ)^2))/6)
  let a:ℝ:=min (lam/(10*d)) (min (θ/(200*(K:ℝ)^2)) (ρ*ε/2))
  let γ:ℝ:=min (eps/2) (min (1/2) (min (lam/(10*d)) (ρ*ε/2)))
  have hdR:(0:ℝ)<d:=by exact_mod_cast hd
  have hKR:(0:ℝ)<K:=by exact_mod_cast hK
  have heps:0<eps:=by dsimp [eps];positivity
  have heps1:eps≤1:=min_le_left _ _
  have hepsrate:3*eps≤lam*(θ/(100*(K:ℝ)^2)):=by
    have hh:=min_le_right 1 (lam*(θ/(100*(K:ℝ)^2))/6)
    have hp:0≤lam*(θ/(100*(K:ℝ)^2)):=by positivity
    dsimp only [eps]
    nlinarith only [hh,hp]
  have ha:0<a:=by dsimp [a];positivity
  have haD:a≤lam/(10*d):=min_le_left _ _
  have haθ:a≤θ/(200*(K:ℝ)^2):=(min_le_right _ _).trans (min_le_left _ _)
  have haScale:a≤ρ*ε/2:=(min_le_right _ _).trans (min_le_right _ _)
  have hγ:0<γ:=by dsimp [γ];positivity
  have hγeps:γ≤eps:=by
    have h:=min_le_left (eps/2) (min (1/2) (min (lam/(10*d)) (ρ*ε/2)))
    dsimp only [γ]
    linarith
  have hγeps2:γ≤eps/2:=min_le_left _ _
  have hd1:(1:ℝ)≤d:=by exact_mod_cast hd
  have hγhalf:γ≤1/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hγD:γ≤lam/(10*d):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hγlam:γ≤lam/10:=by
    have hh:=mul_nonneg hlam.le (sub_nonneg.mpr hd1)
    apply le_trans hγD
    apply (div_le_iff₀ (show 0<10*(d:ℝ) by positivity)).2
    nlinarith only [hh]
  have hγScale:γ≤ρ*ε/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨eps,a,γ,heps,heps1,hepsrate,ha,haD,haθ,hγ,hγeps,hγeps2,hγhalf,hγD,hγlam,?_⟩
  intro n A hA
  have hmax:max a γ≤ρ*ε/2:=max_le haScale hγScale
  have hn:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hm:=mul_le_mul_of_nonneg_right hmax hn
  have hρA:=mul_le_mul_of_nonneg_left hA hρ.le
  nlinarith only [hm,hρA]
end Oberwolfach
