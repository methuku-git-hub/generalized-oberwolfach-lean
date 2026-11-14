module

public import Mathlib.Tactic

@[expose] public section
/-! An absorber of bounded size fits both positive linear loss allowances
once the ambient order is chosen sufficiently large. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_absorber_loss_budget_after_capacity
    (gammaLoss sigmaLoss:ℝ) (hγ:0<gammaLoss) (hσ:0<sigmaLoss) (e₀:ℕ):
    ∃ N:ℕ,1≤N ∧ ∀ n:ℕ,N≤n→
      (e₀:ℝ)≤gammaLoss*n ∧ (e₀:ℝ)≤sigmaLoss*n := by
  obtain ⟨Ng,hNg⟩:=exists_nat_gt ((e₀:ℝ)/gammaLoss)
  obtain ⟨Ns,hNs⟩:=exists_nat_gt ((e₀:ℝ)/sigmaLoss)
  refine ⟨max 1 (max Ng Ns),by omega,?_⟩
  intro n hn
  have hng:(Ng:ℝ)≤n:=by exact_mod_cast (show Ng≤n by omega)
  have hns:(Ns:ℝ)≤n:=by exact_mod_cast (show Ns≤n by omega)
  have hg:(e₀:ℝ)/gammaLoss<(n:ℝ):=hNg.trans_le hng
  have hs:(e₀:ℝ)/sigmaLoss<(n:ℝ):=hNs.trans_le hns
  constructor
  · simpa only [mul_comm] using ((div_lt_iff₀ hγ).mp hg).le
  · simpa only [mul_comm] using ((div_lt_iff₀ hσ).mp hs).le
end Oberwolfach
