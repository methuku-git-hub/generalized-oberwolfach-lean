module

public import Mathlib.Tactic

@[expose] public section
/-! The class-edit tolerance can be chosen after the matching deletion
budget and balanced-correction scale, with room for the existing deletion. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_class_matching_distinct_ordered_scales
    (αHost αAssign ρ₀ ε Δ lam lam₀:ℝ) (hαHost:0<αHost) (hαAssign:0<αAssign) (hρ₀:0<ρ₀) (hε:0<ε)
    (hΔ:0<Δ) (hlam:lam₀<lam):
    ∃δ:ℝ,0<δ ∧ ∀c:ℝ,0<c→∃ξ:ℝ,0<ξ ∧ δ+ξ≤Δ/2 ∧
      ξ≤min (min (c/4) (δ/16)) (αHost*(ρ₀/200)^2/4) ∧
      ξ≤αAssign/32 ∧ ξ/2≤(lam-lam₀)*ε:=by
  let δ:=Δ/4
  have hδ:0<δ:=by dsimp [δ];positivity
  refine ⟨δ,hδ,?_⟩
  intro c hc
  let ξ:=min (δ/16) (min (c/4) (min (αHost*(ρ₀/200)^2/4) (min (αAssign/32) ((lam-lam₀)*ε))))
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have h1:ξ≤δ/16:=min_le_left _ _
  have h2:ξ≤c/4:=(min_le_right _ _).trans (min_le_left _ _)
  have h3:ξ≤αHost*(ρ₀/200)^2/4:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4:ξ≤αAssign/32:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h5:ξ≤(lam-lam₀)*ε:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨ξ,hξ,?_,?_,h4,?_⟩
  · dsimp [δ] at *;linarith
  · exact le_min (le_min h2 h1) h3
  · have hp:0<(lam-lam₀)*ε:=mul_pos (sub_pos.mpr hlam) hε
    linarith
end Oberwolfach
