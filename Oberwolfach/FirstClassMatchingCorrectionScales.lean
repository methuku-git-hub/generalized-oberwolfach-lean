module

public import Mathlib.Tactic

@[expose] public section
/-! The class-edit tolerance can be chosen after the matching deletion
budget and balanced-correction scale, with room for the existing deletion. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_class_matching_correction_scales
    (α ρ₀ ε c Δ lam lam₀:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hε:0<ε)
    (hc:0<c) (hΔ:0<Δ) (hlam:lam₀<lam):
    ∃δ ξ:ℝ,0<δ ∧ 0<ξ ∧ δ+ξ≤Δ/2 ∧
      ξ≤min (min (c/4) (δ/16)) (α*(ρ₀/200)^2/4) ∧
      ξ≤α/32 ∧ ξ/2≤(lam-lam₀)*ε:=by
  let δ:=Δ/4
  let ξ:=min (δ/16) (min (c/4) (min (α*(ρ₀/200)^2/4) (min (α/32) ((lam-lam₀)*ε))))
  have hδ:0<δ:=by dsimp [δ];positivity
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have h1:ξ≤δ/16:=min_le_left _ _
  have h2:ξ≤c/4:=(min_le_right _ _).trans (min_le_left _ _)
  have h3:ξ≤α*(ρ₀/200)^2/4:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4:ξ≤α/32:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h5:ξ≤(lam-lam₀)*ε:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ,ξ,hδ,hξ,?_,?_,h4,?_⟩
  · dsimp [δ] at *;linarith
  · exact le_min (le_min h2 h1) h3
  · have hp:0<(lam-lam₀)*ε:=mul_pos (sub_pos.mpr hlam) hε
    linarith
end Oberwolfach
