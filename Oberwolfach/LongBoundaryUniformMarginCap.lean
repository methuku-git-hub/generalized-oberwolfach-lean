module

public import Oberwolfach.LongBoundaryPreparedNumericCapChoice

@[expose] public section
/-! A cap selected using an upper bound for the matching margin remains valid
when a later selector shrinks that margin, avoiding a circular parameter choice. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach

theorem long_boundary_prepared_uniform_small_margin_cap_choice
    (α lamUpper lamAssign ε δold δlocal ρ₀ θ:ℝ)
    (hα:0<α) (hε:0<ε) (hlam:lamUpper<lamAssign) (hδ:δold<δlocal)
    (htiny:lamUpper<((ρ₀/4)/40000)*θ/4096):
    ∃ξCap:ℝ,0<ξCap ∧ ∀lam:ℝ,lam≤lamUpper→∀ξ':ℝ,ξ'≤ξCap→
      lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mv:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mv),0<mv→
        ξ'*(n:ℝ)≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  obtain ⟨ξCap,hξCap,hcap⟩:=long_boundary_prepared_numeric_cap_choice α lamUpper lamAssign ε δold δlocal ρ₀ θ hα hε hlam hδ htiny
  refine ⟨ξCap,hξCap,?_⟩
  intro lam hle ξ' hξ'
  obtain ⟨hsmall,hgap,hαcap,hinner⟩:=hcap ξ' hξ'
  have hmul: (lamAssign-lamUpper)*ε≤(lamAssign-lam)*ε := by
    exact mul_le_mul_of_nonneg_right (by linarith) hε.le
  exact ⟨by linarith,hgap.trans hmul,hαcap,hinner⟩

theorem long_boundary_ordered_margin_and_cap_choice
    (α lamAssign ε δold δlocal ρ₀ θ:ℝ)
    (hα:0<α) (hassign:0<lamAssign) (hε:0<ε) (hδold:0<δold)
    (hδ:δold<δlocal) (hρ:0<ρ₀) (hθ:0<θ):
    ∃lamUpper ξCap:ℝ,0<lamUpper ∧ 0<ξCap ∧
      lamUpper<lamAssign ∧ lamUpper≤δold*ε/32 ∧ lamUpper≤θ ∧ lamUpper≤α/128 ∧
      lamUpper<((ρ₀/4)/40000)*θ/4096 ∧
    ∀lam:ℝ,lam≤lamUpper→∀ξ':ℝ,ξ'≤ξCap→
      lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
      ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
      ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mv:ℕ) (β:ℝ)
        (Q:Vortex U G D β ε mv),0<mv→
        ξ'*(n:ℝ)≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  let threshold:ℝ:=((ρ₀/4)/40000)*θ/4096
  have hthreshold:0<threshold:=by dsimp [threshold];positivity
  let lamUpper:ℝ:=min (lamAssign/2) (min (δold*ε/64) (min (θ/2) (min (α/256) (threshold/2))))
  have hlam:0<lamUpper:=by dsimp [lamUpper];positivity
  have h1:lamUpper≤lamAssign/2:=min_le_left _ _
  have h2:lamUpper≤δold*ε/64:=(min_le_right _ _).trans (min_le_left _ _)
  have h3:lamUpper≤θ/2:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4:lamUpper≤α/256:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h5:lamUpper≤threshold/2:=(min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hlt:lamUpper<lamAssign:=by linarith
  have htiny:lamUpper<((ρ₀/4)/40000)*θ/4096:=by dsimp [threshold] at h5 hthreshold;linarith
  obtain ⟨ξCap,hξCap,hcap⟩:=long_boundary_prepared_uniform_small_margin_cap_choice α lamUpper lamAssign ε δold δlocal ρ₀ θ hα hε hlt hδ htiny
  refine ⟨lamUpper,ξCap,hlam,hξCap,hlt,?_,?_,?_,htiny,hcap⟩
  · have hh:0<δold*ε:=mul_pos hδold hε
    linarith
  · linarith
  · linarith
end Oberwolfach
