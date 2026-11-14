module

public import Oberwolfach.FirstVortexActiveCeilingRateChoice

@[expose] public section
/-! Choose the assignment rate and a spacing cap before choosing the actual
matching spacing.  Every smaller positive spacing keeps the ceiling margin. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_pre_spacing_assignment_choice
    (ρ ε cap upper:ℝ) (hρ:0<ρ) (hε:0<ε) (hcap:0<cap) (hupper:0<upper):
    ∃lamAssign θcap:ℝ,0<lamAssign ∧ lamAssign≤upper ∧ 0<θcap ∧ θcap≤upper ∧
      ∀θ:ℝ,0≤θ→θ≤θcap→
        8*(θ*ε^2+lamAssign*ε)/((ρ/4)/40000)<cap*ε/128 :=by
  obtain ⟨θcap,lamAssign,hθ,hla,hθup,hlaup,hstrict⟩:=
    first_vortex_active_ceiling_rate_choice ρ ε cap upper hρ hε hcap hupper
  refine ⟨lamAssign,θcap,hla,hlaup,hθ,hθup,?_⟩
  intro θ hθ0 hθcap
  have hden:0<((ρ/4)/40000):=by positivity
  have hmul:=mul_le_mul_of_nonneg_right hθcap (sq_nonneg ε)
  have hnum:8*(θ*ε^2+lamAssign*ε)≤8*(θcap*ε^2+lamAssign*ε):=by linarith
  exact lt_of_le_of_lt (div_le_div_of_nonneg_right hnum hden.le) hstrict
end Oberwolfach
