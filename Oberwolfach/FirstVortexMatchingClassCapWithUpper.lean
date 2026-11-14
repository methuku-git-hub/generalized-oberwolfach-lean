module

public import Oberwolfach.FirstVortexMatchingClassCapChoice

@[expose] public section
/-! Shrink both matching parameters after the level and global budgets are
fixed, while retaining the original physical-edit implications. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_matching_class_cap_with_upper
    (α lamAssign ε δold δlocal θ ρ₀ lamUpper ξUpper:ℝ)
    (hα:0<α) (hAssign:0<lamAssign) (hε:0<ε) (hδ:0<δold)
    (hgap:δold<δlocal) (hθ:0<θ) (hρ:0<ρ₀) (hLamUpper:0<lamUpper) (hξUpper:0<ξUpper):
    ∃lam ξCap:ℝ,0<lam ∧ 0<ξCap ∧ lam≤lamUpper ∧ ξCap≤ξUpper ∧
      lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      ∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ₀/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  obtain ⟨lamOld,ξOld,hlamOld,hξOld,hθOld,hαOld,hδOld,hCap⟩:=
    first_vortex_matching_class_cap_choice α lamAssign ε δold δlocal θ ρ₀
      hα hAssign hε hδ hgap hθ hρ
  let lam:=min lamOld lamUpper
  let ξCap:=min ξOld ξUpper
  have hlam:0<lam:=by dsimp [lam];positivity
  have hξ:0<ξCap:=by dsimp [ξCap];positivity
  have hlamOld':lam≤lamOld:=min_le_left _ _
  have hξOld':ξCap≤ξOld:=min_le_left _ _
  refine ⟨lam,ξCap,hlam,hξ,min_le_right _ _,min_le_right _ _,hlamOld'.trans hθOld,
    hlamOld'.trans hαOld,hlamOld'.trans hδOld,?_⟩
  intro ξ' hξ'
  obtain ⟨hfirst,hsecond,hthird,hfourth⟩:=hCap ξ' (hξ'.trans hξOld')
  refine ⟨by linarith,?_,hthird,hfourth⟩
  have hm:=mul_le_mul_of_nonneg_right (sub_nonneg.mpr hlamOld') hε.le
  nlinarith
end Oberwolfach
