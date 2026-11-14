module

public import Oberwolfach.FirstVortexActiveAndClassCapChoices

@[expose] public section
/-! The matching sampling and assignment rates can be chosen after the
active tolerance and below any later positive local-rate cap. The matching
caller does not require the auxiliary alpha-versus-theta comparison used by
a more restrictive early-rate choice. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_late_active_matching_choices
    (α ε δold δlocal δglobal ρ cap upper:ℝ)
    (hα:0<α) (hε:0<ε) (hδ:0<δold) (hgap:δold<δlocal)
    (hδglobal:0<δglobal) (hρ:0<ρ) (hcap:0<cap) (hupper:0<upper):
    ∃θ lamAssign lam ξCap:ℝ,
      0<θ ∧ 0<lamAssign ∧ θ≤upper ∧ lamAssign≤upper ∧
      10*θ≤δold ∧ θ≤δold/32 ∧ θ≤1/100 ∧ 10*θ≤δglobal ∧
      8*(θ*ε^2+lamAssign*ε)/((ρ/4)/40000)<cap*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      ∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  let bound:ℝ:=min (upper/2) (min (δold/64) (min (δglobal/20) (1/200)))
  have hbound:0<bound:=by dsimp [bound];positivity
  obtain ⟨θ,lamAssign,lam,ξCap,hθ,hAssign,hθbound,hAssignBound,hRate,
    hlam,hξ,hlamθ,hlamα,hlamδ,hCap⟩:=
    first_vortex_active_and_class_cap_choices α ε δold δlocal ρ cap bound
      hα hε hδ hgap hρ hcap hbound
  have hb1:bound≤upper/2:=min_le_left _ _
  have hb2:bound≤δold/64:=(min_le_right _ _).trans (min_le_left _ _)
  have hb3:bound≤δglobal/20:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb4:bound≤1/200:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨θ,lamAssign,lam,ξCap,hθ,hAssign,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,hRate,hlam,hξ,hlamθ,hlamα,hlamδ,hCap⟩
end Oberwolfach
