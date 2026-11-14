module

public import Oberwolfach.RootedGreedyEmbeddings

@[expose] public section

/-! An explicitly ordered finite graph can be specified by its earlier
neighbours. This converts their cardinal bound to the embedding theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def predecessorGraph (B : ℕ → Finset ℕ) (hB : ∀ j,∀ i∈B j,i<j) : SimpleGraph ℕ where
  Adj i j := i∈B j ∨ j∈B i
  symm := ⟨fun _ _ h=>h.symm⟩
  loopless := ⟨fun i h=>by rcases h with h|h <;> exact (lt_irrefl i) (hB i i h)⟩

theorem predecessorGraph_lower_adj (B : ℕ → Finset ℕ) (hB : ∀ j,∀ i∈B j,i<j)
    (i j : ℕ) (hij : i<j) : (predecessorGraph B hB).Adj i j ↔ i∈B j := by
  constructor
  · intro h
    rcases h with h|h
    · exact h
    · exact False.elim (Nat.lt_asymm hij (hB i j h))
  · intro h;exact Or.inl h

theorem predecessorGraph_back_card (B : ℕ → Finset ℕ) (hB : ∀ j,∀ i∈B j,i<j) (n : ℕ) :
    (Finset.univ.filter (fun i : Fin (n+1)=>(predecessorGraph B hB).Adj (i:ℕ) (n+1))).card=(B (n+1)).card := by
  apply Finset.card_bij (fun (i : Fin (n+1)) _=>(i:ℕ))
  · intro i hi
    exact (predecessorGraph_lower_adj B hB _ _ i.isLt).mp (Finset.mem_filter.mp hi).2
  · intro i _ j _ he
    exact Fin.ext he
  · intro j hj
    refine ⟨⟨j,hB (n+1) j hj⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl hj⟩

end Oberwolfach
