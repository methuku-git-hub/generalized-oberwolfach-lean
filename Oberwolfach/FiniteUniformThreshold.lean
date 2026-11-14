module

public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Data.Finset.Max

@[expose] public section
/-! A finite family of thresholds is fixed before choosing the order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem finite_uniform_threshold {I:Type} [Fintype I] (P:I→ℕ→Prop)
    (h:∀ i,∃ N,∀ n,N≤n→P i n):
    ∃ N,∀ i n,N≤n→P i n:=by
  classical
  choose N hN using h
  refine ⟨Finset.univ.sup N,?_⟩
  intro i n hn
  exact hN i n ((Finset.le_sup (Finset.mem_univ i)).trans hn)
end Oberwolfach
