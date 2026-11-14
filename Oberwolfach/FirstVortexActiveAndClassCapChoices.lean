module

public import Oberwolfach.FirstVortexActiveCeilingRateChoice
public import Oberwolfach.FirstVortexMatchingClassCapChoice

@[expose] public section
/-! Choose the active ceiling and the matching class-edit cap together after
both the vortex scale and the desired active tolerance have been fixed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_active_and_class_cap_choices
    (α ε δold δlocal ρ cap upper:ℝ)
    (hα:0<α) (hε:0<ε) (hδ:0<δold) (hgap:δold<δlocal)
    (hρ:0<ρ) (hcap:0<cap) (hupper:0<upper):
    ∃θ lamAssign lam ξCap:ℝ,
      0<θ ∧ 0<lamAssign ∧ θ≤upper ∧ lamAssign≤upper ∧
      8*(θ*ε^2+lamAssign*ε)/((ρ/4)/40000)<cap*ε/128 ∧
      0<lam ∧ 0<ξCap ∧ lam≤θ ∧ lam≤α/128 ∧ lam≤δold*ε/32 ∧
      ∀ξ':ℝ,ξ'≤ξCap→lam+ξ'≤((ρ/4)/40000)*θ/4096 ∧
        ξ'/2≤(lamAssign-lam)*ε ∧ ξ'≤α/32 ∧
        ∀n:ℕ,∀(U:Type) [Fintype U] (G:SimpleGraph (Fin n)) (D mm:ℕ) (β:ℝ)
          (Q:Vortex U G D β ε mm),0<mm→ξ'*n≤(δlocal-δold)*((Q.extendedVertices 1).card:ℝ) :=by
  obtain ⟨θ,lamAssign,hθ,hAssign,hθupper,hAssignUpper,hRate⟩:=
    first_vortex_active_ceiling_rate_choice ρ ε cap upper hρ hε hcap hupper
  obtain ⟨lam,ξCap,hlam,hξ,hlamθ,hlamα,hlamδ,hCap⟩:=
    first_vortex_matching_class_cap_choice α lamAssign ε δold δlocal θ ρ
      hα hAssign hε hδ hgap hθ hρ
  exact ⟨θ,lamAssign,lam,ξCap,hθ,hAssign,hθupper,hAssignUpper,hRate,
    hlam,hξ,hlamθ,hlamα,hlamδ,hCap⟩
end Oberwolfach
