module

public import Oberwolfach.OrdinaryLocalCycles
public import Oberwolfach.TransferCyclePositions

@[expose] public section

/-! Common replacement paths are counted in endpoint-first order. Each
replacement cycle avoids forbidden pairs; the two replaced roots need not
avoid one another in the forbidden graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

def ordinaryPathRequirements (m : ℕ) (x y : V) (n : ℕ) (f : Fin n→V) : Finset V :=
  if h0 : n=0 then {x,y} else if h1 : n=1 then
    if m=2 then {x,y,f ⟨0,by omega⟩} else {x,y}
  else {f ⟨if n=2 then 0 else n-1,by split_ifs  <;> omega⟩}∪
    (if n=m-1 then {f ⟨1,by omega⟩} else ∅)

theorem ordinaryPathRequirements_card (m : ℕ) (x y : V) (n : ℕ) (f : Fin n→V) :
    (ordinaryPathRequirements m x y n f).card  ≤  (if m=2 then 3 else 2) := by
  have h2 : 2 ≤ (if m=2 then 3 else 2) := by split_ifs <;> omega
  unfold ordinaryPathRequirements
  by_cases h0 : n=0
  · rw [dif_pos h0];exact Finset.card_le_two.trans h2
  rw [dif_neg h0]
  by_cases h1 : n=1
  · rw [dif_pos h1]
    by_cases hm2 : m=2
    · rw [if_pos hm2,if_pos hm2];exact Finset.card_le_three
    · rw [if_neg hm2];exact Finset.card_le_two.trans h2
  rw [dif_neg h1]
  apply le_trans _ h2
  by_cases hl : n=m-1
  · rw [if_pos hl,Finset.singleton_union];exact Finset.card_le_two
  · rw [if_neg hl,Finset.union_empty,Finset.card_singleton];omega

def commonPathOrder (m : ℕ) (hm : 2 ≤ m) : Fin m ↪ Fin m where
  toFun i := ⟨transferColumnOrder (m+1) (i.val+1),by
    simpa only [Nat.add_sub_cancel] using transferColumnOrder_bound (m+1) (i.val+1) (by omega) (by omega) (by omega)⟩
  inj' := by
    intro i j h
    have hh := congrArg (fun z : Fin m=>z.val) h
    have h' := transferColumnOrder_injective (m+1) (i.val+1) (j.val+1) (by omega)
      (by omega) (by omega) (by omega) (by omega) hh
    exact Fin.ext (by omega)

theorem commonPathOrder_surjective (m : ℕ) (hm : 2 ≤ m) : Function.Surjective (commonPathOrder m hm) :=
  Finite.surjective_of_injective (commonPathOrder m hm).injective

variable {m : ℕ} (Q F : SimpleGraph V) (T : Finset V) (x y : V)
    (f : Fin m→V) (hf : SparseGreedyGood Q F T {x,y} (ordinaryPathRequirements m x y) f)
include hf

theorem ordinaryCommonPath_endpoint (hm : 2 ≤ m) (z : V) (hz : z=x ∨ z=y) (i : Fin m)
    (hi : i.val=0 ∨ i.val=1) : Q.Adj z (f i) := by
  apply hf.2.2.2.2 i
  rcases hi with hi|hi
  · simp only [ordinaryPathRequirements,hi,dite_true,Finset.mem_insert,Finset.mem_singleton]
    exact hz
  · simp only [ordinaryPathRequirements,hi,show (1:ℕ)≠0 by omega,dite_false,dite_true]
    split_ifs  <;> simp only [Finset.mem_insert,Finset.mem_singleton]  <;> tauto

theorem ordinaryCommonPath_step (hm : 2 ≤ m) (j : ℕ) (hj : 1 ≤ j) (hjm : j < m) :
    Q.Adj (f ⟨transferColumnOrder (m+1) j,by
      simpa only [Nat.add_sub_cancel] using transferColumnOrder_bound (m+1) j (by omega) (by omega) (by omega)⟩)
      (f ⟨transferColumnOrder (m+1) (j+1),by
      simpa only [Nat.add_sub_cancel] using transferColumnOrder_bound (m+1) (j+1) (by omega) (by omega) (by omega)⟩) := by
  by_cases hj1 : j=1
  · subst j
    by_cases hm2 : m=2
    · subst m
      have hh := hf.2.2.2.2 (⟨1,by omega⟩ : Fin 2)
        (f ⟨0,by omega⟩) (by simp [ordinaryPathRequirements,greedyPrefix])
      simpa only [transferColumnOrder,ite_true,show (2:ℕ)≠1 by omega,ite_false,show 2+1-1=2 by omega] using hh
    · have hh := hf.2.2.2.2 (⟨2,by omega⟩ : Fin m)
        (f ⟨0,by omega⟩) (by simp [ordinaryPathRequirements,greedyPrefix])
      simpa only [transferColumnOrder,ite_true,show (2:ℕ)≠1 by omega,
        show 2≠m+1-1 by omega,ite_false] using hh
  · by_cases hjlast : j+1=m
    · have hh := hf.2.2.2.2 (⟨j,hjm⟩ : Fin m) (f ⟨1,by omega⟩) (by
        unfold ordinaryPathRequirements
        rw [dif_neg (show j≠0 by omega),dif_neg hj1,if_pos (show j=m-1 by omega)]
        exact Finset.mem_union_right _ (Finset.mem_singleton.mpr rfl))
      convert hh.symm using 1  <;> congr 1  <;> apply Fin.ext  <;>
        simp only [transferColumnOrder] <;> split_ifs <;> omega
    · have hh := hf.2.2.2.2 (⟨j+1,by omega⟩ : Fin m) (f ⟨j,hjm⟩) (by
        simp only [ordinaryPathRequirements,show j+1≠0 by omega,show j+1≠1 by omega,dite_false,
          show j+1≠2 by omega,ite_false,Finset.mem_union,Finset.mem_singleton]
        left;rfl)
      convert hh using 1  <;> congr 1  <;> apply Fin.ext  <;>
        simp only [transferColumnOrder,hj1,show j≠m+1-1 by omega,
          show j+1≠1 by omega,show j+1≠m+1-1 by omega,ite_false]

end Oberwolfach
