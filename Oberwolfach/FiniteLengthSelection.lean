module

public import Oberwolfach.FiniteUniformThreshold
public import Mathlib.Data.Fintype.Powerset

@[expose] public section
/-! A bounded set of permitted lengths may be chosen after the common order
threshold, by taking the maximum over all its possible subsets. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem finite_length_selection_uniform_threshold (K:ℕ)
    (P:Finset (Fin K)→ℕ→Prop)
    (h:∀ S,∃ N,∀ n,N≤n→P S n):
    ∃ N,∀ n,N≤n→∀ S,P S n:=by
  classical
  obtain ⟨N,hN⟩:=finite_uniform_threshold P h
  exact ⟨N,fun n hn S=>hN S n hn⟩
end Oberwolfach
