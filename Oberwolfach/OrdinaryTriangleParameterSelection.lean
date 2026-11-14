module

public import Oberwolfach.OrdinaryTriangleParentBalance

@[expose] public section
/-! A single sufficiently small positive constant makes the prescribed-edge,
hub and triangle budgets compatible. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_parameter_selection
    (a₀ ε₀ θ ρhub ρ ω p η γ:ℝ)
    (ha₀:0<a₀) (hε₀:0<ε₀) (hθ:0<θ) (hρhub:0<ρhub) (hρ:0<ρ)
    (hω:0<ω) (hp:0<p) (hη:0<η) (hγ:0<γ):
    ∃ κ:ℝ,0<κ ∧ κ≤a₀ ∧ κ≤ε₀ ∧ κ≤θ ∧ 13*κ≤ρhub ∧ 54*κ≤ρ ∧
      3*κ≤2*ω*p*η ∧ 48*κ≤p^6*γ*min 1 ω:=by
  let κ:=min a₀ (min ε₀ (min θ (min (ρhub/13) (min (ρ/54)
    (min (2*ω*p*η/3) (p^6*γ*min 1 ω/48))))))
  have hκ:0<κ:=by dsimp [κ];positivity
  have h1:κ≤a₀:=min_le_left _ _
  have h2:κ≤ε₀:=(min_le_right _ _).trans (min_le_left _ _)
  have h3:κ≤θ:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4:κ≤ρhub/13:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h5:κ≤ρ/54:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have h6:κ≤2*ω*p*η/3:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have h7:κ≤p^6*γ*min 1 ω/48:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  refine ⟨κ,hκ,h1,h2,h3,?_,?_,?_,?_⟩ <;> linarith
end Oberwolfach
