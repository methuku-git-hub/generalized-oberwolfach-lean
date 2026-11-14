module

public import Oberwolfach.OrdinaryTriangleInnerNumericHierarchy

@[expose] public section
/-! A single terminal-size threshold absorbs the finite conflict degree,
inner-factor size, and quadratic index-count requirements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_inner_terminal_threshold
    (ε lam:ℝ) (hε:0<ε) (hlam:0<lam) (b₀ N₀:ℕ):
    ∃M:ℕ,N₀≤M ∧ 32≤M ∧ 4/ε≤(M:ℝ) ∧ (b₀:ℝ)≤lam*M:=by
  obtain ⟨N,hN⟩:=exists_nat_gt (max (4/ε) ((b₀:ℝ)/lam))
  let M:=max 32 (max N₀ N)
  have hNM:(N:ℝ)≤M:=by exact_mod_cast (show N≤M by dsimp [M];omega)
  have hεM:4/ε≤(M:ℝ):=(le_max_left _ _).trans (hN.le.trans hNM)
  have hbM:(b₀:ℝ)/lam≤M:=(le_max_right _ _).trans (hN.le.trans hNM)
  have hb:(b₀:ℝ)≤lam*M:=by
    have hh:=(div_le_iff₀ hlam).mp hbM
    nlinarith only [hh]
  exact ⟨M,by dsimp [M];omega,by dsimp [M];omega,hεM,hb⟩
end Oberwolfach
