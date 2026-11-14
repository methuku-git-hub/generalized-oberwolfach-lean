module

public import Oberwolfach.FirstVortexMatchingOrderedChoices

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_joint_margins
    (d K:ℕ) (lam θ ε δ:ℝ) (hd:0<d) (hK:0<K)
    (hlam:0<lam) (hθ:0<θ) (hε:0<ε) (hδ:0<δ):
    ∃ρ eps a γ:ℝ,0<ρ ∧ ρ≤θ/4096 ∧
      0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      0<a ∧ a≤lam/(10*d) ∧ a≤θ/(200*(K:ℝ)^2) ∧
      0<γ ∧ γ≤eps ∧ γ≤eps/2 ∧ γ≤1/2 ∧ γ≤lam/(10*d) ∧ γ≤lam/10 ∧
      ∀(n A:ℕ), ε*n/2≤A→max a γ*n≤ρ*A ∧ 2*(max a γ*n)≤δ*A/4:=by
  let ρ:ℝ:=min (θ/4096) (δ/8)
  have hρ:0<ρ:=by dsimp [ρ];positivity
  have hρθ:ρ≤θ/4096:=min_le_left _ _
  have hρδ:ρ≤δ/8:=min_le_right _ _
  obtain ⟨eps,a,γ,heps,heps1,hepsrate,ha,haD,haθ,hγ,hγeps,hγeps2,hγhalf,hγD,hγlam,hscale⟩:=
    first_vortex_matching_ordered_choices d K lam θ ε ρ hd hK hlam hθ hε hρ
  refine ⟨ρ,eps,a,γ,hρ,hρθ,heps,heps1,hepsrate,ha,haD,haθ,hγ,hγeps,hγeps2,hγhalf,hγD,hγlam,?_⟩
  intro n A hA
  have hs:=hscale n A hA
  have hm:=mul_le_mul_of_nonneg_right hρδ (show (0:ℝ)≤A by positivity)
  exact ⟨hs,by nlinarith only [hs,hm]⟩
end Oberwolfach
