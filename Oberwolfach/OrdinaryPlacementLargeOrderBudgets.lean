module

public import Oberwolfach.ApproximateSublinearMargin
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section
/-! The concentration and embedding-size requirements use one threshold
chosen from the placement parameters before the graph and the sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_placement_large_order_budgets (αcap lam δ:ℝ) (hα:0<αcap):
    ∃N:ℕ,∀n:ℕ,N≤n→
      (n:ℝ)^(3/4:ℝ)≤αcap*n ∧ 100/(lam/2)≤(n:ℝ) ∧ 2/Real.sqrt δ≤(n:ℝ) :=by
  obtain ⟨N₁,h₁⟩:=eventually_three_quarters_and_constant_le_linear αcap 0 hα
  obtain ⟨N₂,h₂⟩:=eventually_constant_le_linear (100/(lam/2)) 1 (by norm_num)
  obtain ⟨N₃,h₃⟩:=eventually_constant_le_linear (2/Real.sqrt δ) 1 (by norm_num)
  refine ⟨max N₁ (max N₂ N₃),?_⟩
  intro n hn
  have ha:=h₁ n (by omega)
  have hb:=h₂ n (by omega)
  have hc:=h₃ n (by omega)
  simpa using (show (n:ℝ)^(3/4:ℝ)+0≤αcap*n ∧ 100/(lam/2)≤(1:ℝ)*n ∧ 2/Real.sqrt δ≤(1:ℝ)*n from ⟨ha,hb,hc⟩)
end Oberwolfach
