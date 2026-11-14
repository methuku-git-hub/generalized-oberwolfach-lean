module

public import Oberwolfach.OrdinaryPositionalBudget

@[expose] public section
/-! The separation and degree-error budgets hold simultaneously for every
short length, with one threshold independent of the chosen subset. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem selected_lengths_positional_budgets (K b:ℕ) (r:Fin K→ℕ) (B:Fin K→ℝ)
    (hB:∀ i,0≤B i) (τ:ℝ) (hτ:0<τ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ D ε:ℝ,(n:ℝ)/2≤D→ε≤τ/4→∀ i:Fin K,
      5*(r i:ℝ)^4*B i*(2*b)/(n:ℝ)≤τ ∧
      6*(r i:ℝ)^4*B i*(2*b)+ε*(n:ℝ)≤τ*D:=by
  classical
  have hex (i:Fin K):=ordinary_positional_error_budget (r i) b (B i) τ (hB i) hτ
  choose Ni hNi using hex
  refine ⟨Finset.univ.sup Ni,?_⟩
  intro n hn D ε hD hε i
  exact hNi i n ((Finset.le_sup (Finset.mem_univ i)).trans hn) D ε hD hε
end Oberwolfach
