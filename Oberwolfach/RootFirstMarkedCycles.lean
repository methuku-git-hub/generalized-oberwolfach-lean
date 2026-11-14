module

public import Oberwolfach.MarkedRootOrder
public import Oberwolfach.SuccessorTupleRepresentation

@[expose] public section

/-! Root-first and canonical coordinates describe the same typed directed
cycle. The order change preserves adjacency and the separated vertex set. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Oberwolfach

variable {V E K : Type*} {tail head : E → V} {ktail khead : K → V}
    {m : ℕ} {π : Equiv.Perm V} {b : ℕ}

def IsRootFirstMarkedCycle (tail head : E → V) (ktail khead : K → V)
    (m : ℕ) (π : Equiv.Perm V) (b : ℕ) (s : Fin (m+1)) (f : Fin (m+1) → V) : Prop :=
  PermutationSeparated π b f ∧ ∀ t : Fin (m+1),
    if t=s then ∃ e,ktail e=f t ∧ khead e=f (finRotate (m+1) t)
    else ∃ e,tail e=f t ∧ head e=f (finRotate (m+1) t)

theorem markedCycle_reindex_iff (σ : Equiv.Perm (Fin (m+1)))
    (hσ : ∀ t,σ (finRotate (m+1) t)=finRotate (m+1) (σ t))
    (f : Fin (m+1) → V) :
    IsMarkedCycleTuple tail head ktail khead m π b (fun t=>f (σ t)) ↔
      IsRootFirstMarkedCycle tail head ktail khead m π b (σ (Fin.last m)) f := by
  constructor
  · intro h
    refine ⟨(permutationSeparated_comp_equiv π b σ f).mp h.1,?_⟩
    intro t
    by_cases ht : t=σ (Fin.last m)
    · rw [if_pos ht,ht,← hσ,finRotate_last]
      exact h.2.2
    · rw [if_neg ht]
      have hnot : σ.symm t≠Fin.last m := by
        intro he
        apply ht
        rw [← he,Equiv.apply_symm_apply]
      obtain ⟨i,hi⟩ := Fin.eq_castSucc_of_ne_last hnot
      have hit : σ i.castSucc=t := by rw [hi,Equiv.apply_symm_apply]
      have his : σ i.succ=finRotate (m+1) t := by
        rw [← finRotate_castSucc_eq_succ,hσ,hit]
      simpa only [hit,his] using h.2.1 i
  · intro h
    refine ⟨(permutationSeparated_comp_equiv π b σ f).mpr h.1,?_,?_⟩
    · intro i
      have hne : σ i.castSucc≠σ (Fin.last m) := fun he=>Fin.castSucc_ne_last i (σ.injective he)
      have hh := h.2 (σ i.castSucc)
      rw [if_neg hne,← hσ,finRotate_castSucc_eq_succ] at hh
      exact hh
    · have hh := h.2 (σ (Fin.last m))
      rw [if_pos rfl,← hσ,finRotate_last] at hh
      exact hh

theorem rootedCycleOrder_marked_iff (j : Bool) (v : V) (z : Fin m → V) :
    IsMarkedCycleTuple tail head ktail khead m π b
      (rootedCycleOrder (markedRootOrder m j) v z) ↔
    IsRootFirstMarkedCycle tail head ktail khead m π b
      (if j then Fin.last m else 2) (Fin.cases v z) := by
  unfold rootedCycleOrder
  rw [markedCycle_reindex_iff _ (markedRootOrder_successor m j)]
  cases j
  · rw [markedRootOrder_marked_tail];rfl
  · rfl

end Oberwolfach
