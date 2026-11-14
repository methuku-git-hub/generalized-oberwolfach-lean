module

public import Oberwolfach.OrdinarySequentialResourceSelection

@[expose] public section
/-! Sequential resource choices with stage-dependent size bounds. Each
forbidden budget is the initial budget plus earlier actual upper bounds. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_sequential_variable_budget_selection
    (l q:ℕ) (bound:Fin l→ℕ) (L:Finset (Sym2 V⊕(V×U)))
    (hrows:(ordinaryResourceRows L).card≤q) (hhubs:(ordinaryResourceHubs L).card≤q)
    (P:Fin l→Finset (Sym2 V⊕(V×U))→Prop)
    (hchoose:∀ (i:Fin l) (L':Finset (Sym2 V⊕(V×U))),
      (ordinaryResourceRows L').card≤q+∑ j∈Finset.univ.filter (fun j:Fin l=>j.val < i.val),bound j →
      (ordinaryResourceHubs L').card≤q+∑ j∈Finset.univ.filter (fun j:Fin l=>j.val < i.val),bound j →
      ∃ T,P i T∧(ordinaryResourceRows T).card+(ordinaryResourceHubs T).card≤bound i∧Disjoint T L'):
    ∃ T:Fin l→Finset (Sym2 V⊕(V×U)),
      (∀ i,P i (T i)∧(ordinaryResourceRows (T i)).card+(ordinaryResourceHubs (T i)).card≤bound i∧Disjoint (T i) L) ∧
      (∀ i j,i≠j→Disjoint (T i) (T j)) :=by
  let allowed:=fun i T=>P i T∧(ordinaryResourceRows T).card+(ordinaryResourceHubs T).card≤bound i∧Disjoint T L
  obtain ⟨T,hT,hdis⟩:=sequential_select_prefix l allowed Disjoint ∅ (by
    intro i T hT
    let s:=Finset.univ.filter (fun j:Fin l=>j.val < i.val)
    let used:=s.biUnion T
    have hr:(ordinaryResourceRows used).card≤∑ j∈s,bound j:=by
      rw [ordinaryResourceRows_biUnion]
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro j hj
      have hh:=(hT.2.1 j (Finset.mem_filter.mp hj).2).2.1
      omega
    have hu:(ordinaryResourceHubs used).card≤∑ j∈s,bound j:=by
      rw [ordinaryResourceHubs_biUnion]
      apply Finset.card_biUnion_le.trans
      apply Finset.sum_le_sum
      intro j hj
      have hh:=(hT.2.1 j (Finset.mem_filter.mp hj).2).2.1
      omega
    have hr':(ordinaryResourceRows (L∪used)).card≤q+∑ j∈s,bound j:=by
      rw [ordinaryResourceRows_union]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add hrows hr)
    have hu':(ordinaryResourceHubs (L∪used)).card≤q+∑ j∈s,bound j:=by
      rw [ordinaryResourceHubs_union]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add hhubs hu)
    obtain ⟨K,hK,hKsize,hKdis⟩:=hchoose i (L∪used) hr' hu'
    refine ⟨K,⟨hK,hKsize,(Finset.disjoint_union_right.mp hKdis).1⟩,?_⟩
    intro j hj
    exact ((Finset.disjoint_union_right.mp hKdis).2.mono_right
      (Finset.subset_biUnion_of_mem T (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩))).symm)
  refine ⟨T,hT,?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h|h
  · exact hdis i j h
  · exact (hdis j i h).symm
end Oberwolfach
