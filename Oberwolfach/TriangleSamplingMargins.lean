module

public import Mathlib.Tactic

@[expose] public section

/-! The deletion tolerance is fixed before the order and the realized
root sets. It pays both count losses and the unchanged-weight potential loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem triangle_sampling_margins (ε₀ τ η K C κ:ℝ)
    (hε:0<ε₀) (hτ:0<τ) (hη:0<η) (hK:0<K) (hC:0<C) (hκ:0<κ):
    ∃ ρ:ℝ,0<ρ ∧ ∀ a b L:ℝ,0<a → κ*a≤b → 0≤L → L≤ρ*a →
      L≤τ*a ∧ (ε₀/4)*a+7*L≤(ε₀/2)*a ∧ (ε₀/4)*b+3*L≤(ε₀/2)*b ∧
      η/8+K*L/a+(η/8+5*C*L/a)≤η/2:=by
  let ρ:=min τ (min (ε₀/28) (min (ε₀*κ/12) (η/(4*(K+5*C)))))
  have hρ:0<ρ:=by dsimp [ρ];positivity
  refine ⟨ρ,hρ,?_⟩
  intro a b L ha hba hL hLρ
  have h₁:ρ≤τ:=min_le_left _ _
  have h₂:ρ≤ε₀/28:=(min_le_right _ _).trans (min_le_left _ _)
  have h₃:ρ≤ε₀*κ/12:=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h₄:ρ≤η/(4*(K+5*C)):=(min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨hLρ.trans (mul_le_mul_of_nonneg_right h₁ ha.le),?_,?_,?_⟩
  · have hh:=hLρ.trans (mul_le_mul_of_nonneg_right h₂ ha.le)
    nlinarith only [hh]
  · have hh:=hLρ.trans (mul_le_mul_of_nonneg_right h₃ ha.le)
    have hb:=mul_le_mul_of_nonneg_left hba hε.le
    nlinarith only [hh,hb]
  · have hh:L/a≤η/(4*(K+5*C)):=((div_le_iff₀ ha).mpr hLρ).trans h₄
    have hd:0<4*(K+5*C):=by positivity
    have hbound:=(le_div_iff₀ hd).mp hh
    have he:K*L/a+5*C*L/a=(K+5*C)*(L/a):=by ring
    nlinarith only [hbound,he]

end Oberwolfach
