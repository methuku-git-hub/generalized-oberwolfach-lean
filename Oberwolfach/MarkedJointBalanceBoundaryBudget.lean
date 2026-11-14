module

public import Oberwolfach.MarkedLocalizedBalanceBudgetChoice

@[expose] public section
/-! A single positive local allowance works for both balance transfer and
boundary row transfer. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_joint_balance_boundary_budget
    (m h:ℕ) (etaBal x:ℝ) (hη:0<etaBal) (hx:0<x):
    ∃c:ℝ,0<c ∧ 2*(h:ℝ)*c≤x/4 ∧
      ∀(V:Type) [Fintype V] [DecidableEq V] (A:Finset V),
      2*(c*A.card)+((m+2:ℕ):ℝ)*(c*A.card)≤
        min ((x/4)*Fintype.card V) ((etaBal/2)*A.card) :=by
  obtain ⟨c₀,ζ,hc₀,hζ,hglobal,hbudget⟩:=marked_localized_balance_budget_choice m etaBal x hη hx
  let c:=min c₀ (x/(16*((h:ℝ)+1)))
  have hc:0<c:=by dsimp [c];positivity
  have hc0:c≤c₀:=min_le_left _ _
  have hcx:c≤x/(16*((h:ℝ)+1)):=min_le_right _ _
  have hcscale:2*(h:ℝ)*c≤x/4:=by
    have ht:=mul_le_mul_of_nonneg_left hcx (show (0:ℝ)≤2*(h:ℝ) by positivity)
    have hdiv:2*(h:ℝ)*(x/(16*((h:ℝ)+1)))≤x/4:=by
      have hh:(0:ℝ)≤h:=by positivity
      rw [←mul_div_assoc]
      apply (div_le_iff₀ (show (0:ℝ)<16*((h:ℝ)+1) by positivity)).mpr
      nlinarith [mul_nonneg hx.le hh]
    exact ht.trans hdiv
  refine ⟨c,hc,hcscale,?_⟩
  intro V _ _ A
  have hn:(0:ℝ)≤A.card:=Nat.cast_nonneg _
  have hh:=mul_le_mul_of_nonneg_right hc0 hn
  have hm:(0:ℝ)≤((m+2:ℕ):ℝ):=by positivity
  have hmul:=mul_le_mul_of_nonneg_left hh hm
  exact (by nlinarith : 2*(c*A.card)+((m+2:ℕ):ℝ)*(c*A.card)≤
    2*(c₀*A.card)+((m+2:ℕ):ℝ)*(c₀*A.card)).trans (hbudget V A)
end Oberwolfach
