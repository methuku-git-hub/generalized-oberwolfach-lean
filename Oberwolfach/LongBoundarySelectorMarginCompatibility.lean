module

public import Oberwolfach.LongBoundaryUniformMarginCap

@[expose] public section
/-! The structural selector later replaces its supplied margin by a minimum.
The boundary cap can be chosen first and remains valid for that exact minimum. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem long_boundary_selector_margin_compatibility
    (α lamAssign ε δold δlocal ρ₀ θ:ℝ)
    (hα:0<α) (hassign:0<lamAssign) (hε:0<ε) (hδold:0<δold)
    (hδ:δold<δlocal) (hρ:0<ρ₀) (hθ:0<θ):
    ∃lamUpper ξCap:ℝ,0<lamUpper ∧ 0<ξCap ∧
    ∀epsOrd:ℝ,0<epsOrd→
    let lam:=min lamUpper epsOrd;
    0<lam ∧ lam<lamAssign ∧ lam≤δold*ε/32 ∧ lam≤θ ∧ lam≤α/128 ∧
    lam<((ρ₀/4)/40000)*θ/4096 ∧
    ∀ξ':ℝ,ξ'≤ξCap→
      lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mv:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mv),0<mv→
        ξ'*(n:ℝ)≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  obtain ⟨lamUpper,ξCap,hlam,hξ,hassign',hlocal,hθcap,hαcap,htiny,hcap⟩:=
    long_boundary_ordered_margin_and_cap_choice α lamAssign ε δold δlocal ρ₀ θ hα hassign hε hδold hδ hρ hθ
  refine ⟨lamUpper,ξCap,hlam,hξ,?_⟩
  intro epsOrd heps lam
  have hle:lam≤lamUpper:=min_le_left _ _
  refine ⟨lt_min hlam heps,lt_of_le_of_lt hle hassign',hle.trans hlocal,hle.trans hθcap,hle.trans hαcap,
    lt_of_le_of_lt hle htiny,?_⟩
  exact hcap lam hle
end Oberwolfach
