module

public import Oberwolfach.OrdinaryVariableBudgetSelection

@[expose] public section
/-! A recursive budget fixes each stage's forbidden-set allowance before
selection; the next allowance includes the previous transformer's bound. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryRecursiveBudget (q:ℕ) (bound:ℕ→ℕ):ℕ→ℕ
  | 0=>q
  | n+1=>ordinaryRecursiveBudget q bound n+bound (q+ordinaryRecursiveBudget q bound n)

theorem ordinary_recursive_budget_sum (q:ℕ) (bound:ℕ→ℕ) (n:ℕ):
    ordinaryRecursiveBudget q bound n=q+∑ j∈Finset.range n,bound (q+ordinaryRecursiveBudget q bound j):=by
  induction n with
  | zero=>simp [ordinaryRecursiveBudget]
  | succ n ih=>simp only [ordinaryRecursiveBudget,Finset.sum_range_succ,ih];omega

theorem ordinary_prefix_budget_sum (l q:ℕ) (bound:ℕ→ℕ) (i:Fin l):
    ordinaryRecursiveBudget q bound i.val=q+
      ∑ j∈Finset.univ.filter (fun j:Fin l=>j.val < i.val),bound (q+ordinaryRecursiveBudget q bound j.val):=by
  rw [ordinary_recursive_budget_sum]
  congr 1
  symm
  apply Finset.sum_bij (fun j _=>j.val)
  · intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  · intro j _ j' _ h
    exact Fin.ext h
  · intro j hj
    have hi:j<l:=(Finset.mem_range.mp hj).trans i.isLt
    let j':Fin l:=⟨j,hi⟩
    exact ⟨j',Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_range.mp hj⟩,rfl⟩
  · intro j _
    rfl

theorem ordinary_sequential_recursive_budget_selection
    (l q:ℕ) (bound:ℕ→ℕ) (L:Finset (Sym2 V⊕(V×U)))
    (hrows:(ordinaryResourceRows L).card≤q) (hhubs:(ordinaryResourceHubs L).card≤q)
    (P:Fin l→Finset (Sym2 V⊕(V×U))→Prop)
    (hchoose:∀ (i:Fin l) (L':Finset (Sym2 V⊕(V×U))),
      (ordinaryResourceRows L').card≤ordinaryRecursiveBudget q bound i.val →
      (ordinaryResourceHubs L').card≤ordinaryRecursiveBudget q bound i.val →
      ∃ T,P i T∧(ordinaryResourceRows T).card+(ordinaryResourceHubs T).card≤
        bound (q+ordinaryRecursiveBudget q bound i.val)∧Disjoint T L'):
    ∃ T:Fin l→Finset (Sym2 V⊕(V×U)),
      (∀ i,P i (T i)∧(ordinaryResourceRows (T i)).card+(ordinaryResourceHubs (T i)).card≤
        bound (q+ordinaryRecursiveBudget q bound i.val)∧Disjoint (T i) L) ∧
      (∀ i j,i≠j→Disjoint (T i) (T j)):=by
  apply ordinary_sequential_variable_budget_selection l q
    (fun i=>bound (q+ordinaryRecursiveBudget q bound i.val)) L hrows hhubs P
  intro i L' hr hu
  apply hchoose i L'
  · rw [←ordinary_prefix_budget_sum l q bound i] at hr
    exact hr
  · rw [←ordinary_prefix_budget_sum l q bound i] at hu
    exact hu
end Oberwolfach
