module

public import Oberwolfach.LongBoundaryPreparedNumericCapChoice

@[expose] public section
/-! The strict margins used by the long boundary cap are achievable by
choosing the internal scales in order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach

theorem long_boundary_early_numeric_choices
    (α ε ρ₀ θ lamMax δold δglobal:ℝ)
    (hα:0<α) (hε:0<ε) (hρ₀:0<ρ₀) (hθ:0<θ) (hMax:0<lamMax)
    (hδold:0<δold) (hδgap:δold<δglobal):
    ∃lam lamAssign δlocal ξCap:ℝ,
      0<lam ∧ lam ≤ lamMax ∧ lam ≤ θ ∧ lam ≤ δold*ε/32 ∧
      lam<((ρ₀/4)/40000)*θ/4096 ∧ lam<lamAssign ∧
      δold<δlocal ∧ δlocal<δglobal ∧ 0<ξCap ∧
    ∀ξ':ℝ,ξ' ≤ ξCap  →  lam+ξ' ≤ ((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2 ≤ (lamAssign-lam)*ε ∧ ξ' ≤ α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mv:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mv),0<mv  → 
        ξ'*(n:ℝ) ≤ (δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  let tiny:ℝ:=((ρ₀/4)/40000)*θ/4096
  have htiny:0<tiny:=by dsimp [tiny];positivity
  let lam:ℝ:=min (lamMax/2) (min (θ/2) (min (tiny/2) (δold*ε/64)))
  have hlam:0<lam:=by dsimp [lam];positivity
  have hlamMax:lam ≤ lamMax/2:=min_le_left _ _
  have hlamθ:lam ≤ θ/2:=(min_le_right _ _).trans (min_le_left _ _)
  have hlamtiny:lam ≤ tiny/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hlamδ:lam ≤ δold*ε/64:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let lamAssign:ℝ:=2*lam
  let δlocal:ℝ:=(δold+δglobal)/2
  have hlamAssign:lam<lamAssign:=by dsimp [lamAssign];linarith
  have hδlocal:δold<δlocal:=by dsimp [δlocal];linarith
  have hδglobal:δlocal<δglobal:=by dsimp [δlocal];linarith
  have hlamTiny:lam<((ρ₀/4)/40000)*θ/4096:=by dsimp [tiny] at *;linarith
  obtain ⟨ξCap,hξCap,hcap⟩:=long_boundary_prepared_numeric_cap_choice α lam lamAssign ε δold δlocal ρ₀ θ
    hα hε hlamAssign hδlocal hlamTiny
  refine ⟨lam,lamAssign,δlocal,ξCap,hlam,?_,?_,?_,hlamTiny,hlamAssign,hδlocal,hδglobal,hξCap,hcap⟩
  · linarith
  · linarith
  · have hh:0 ≤ δold*ε:=mul_nonneg hδold.le hε.le
    nlinarith only [hlamδ,hh]
end Oberwolfach
