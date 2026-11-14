module

public import Oberwolfach.MarkedLocalizedBalanceBudgetChoice

@[expose] public section
/-! The ambient cap is fixed before the relative inner-balance tolerance;
the relative cap may then be chosen later without changing it. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_localized_balance_ordered_caps
    (m:ℕ) (x:ℝ) (hx:0<x):
    ∃ζmax:ℝ,0<ζmax ∧ ((m+4:ℕ):ℝ)*ζmax≤x/4 ∧
    ∀etaBal:ℝ,0<etaBal→∃c:ℝ,0<c ∧
      ∀(V:Type) [Fintype V] [DecidableEq V] (A:Finset V),
      2*(c*A.card)+((m+2:ℕ):ℝ)*(c*A.card)≤
        min ((x/4)*Fintype.card V) ((etaBal/2)*A.card) :=by
  let M:ℝ:=(m+4:ℕ)
  have hM:0<M:=by dsimp [M];positivity
  let ζmax:=x/(8*M)
  have hz:0<ζmax:=by dsimp [ζmax];positivity
  have hbound:M*ζmax≤x/4:=by dsimp [ζmax];field_simp;linarith
  refine ⟨ζmax,hz,by simpa only [M] using hbound,?_⟩
  intro etaBal hη
  obtain ⟨c,_,hc,_,_,hlocal⟩:=marked_localized_balance_budget_choice m etaBal x hη hx
  exact ⟨c,hc,hlocal⟩
end Oberwolfach
