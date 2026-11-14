module

public import Oberwolfach.MarkedPathChoiceEdges

@[expose] public section

/-! Reorder the greedy choices into the actual free path. The opening
and closing constraints are verified for both roots without requiring the
roots to be separated. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pathChoiceOrder_val (r : ℕ) (i : Fin (r+2)) :
    (pathChoiceOrder r i).val=if i.val=0 then 0 else if i.val=r+1 then 1 else i.val+1 := by
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [pathChoiceOrder_zero]
  · rw [pathChoiceOrder_succ]
    by_cases hj : j=Fin.last r
    · subst j;rw [finRotate_last];simp
    · have hv : j.val≠r := by intro h;apply hj;exact Fin.ext h
      rw [Fin.val_succ,coe_finRotate_of_ne_last hj]
      simp only [Fin.val_succ]
      split_ifs <;> omega

theorem permutationSeparated_cons {V : Type*} {m : ℕ}
    (π : Equiv.Perm V) (b : ℕ) (v : V) (f : Fin m→V)
    (hsep : PermutationSeparated π b f) (hroot : ∀ i,¬PermutationClose π b v (f i)) :
    PermutationSeparated π b (Fin.cons v f) := by
  intro i
  refine Fin.cases ?_ (fun i=>?_) i
  · intro j
    refine Fin.cases ?_ (fun j=>?_) j
    · intro hij;exact (hij rfl).elim
    · intro _;exact hroot j
  · intro j
    refine Fin.cases ?_ (fun j=>?_) j
    · intro _;rw [permutationClose_symm];exact hroot i
    · intro hij;exact hsep i j (fun h=>hij (congrArg Fin.succ h))

def DenseRootMarkedPath {V : Type*} (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (j : Bool) (T₀ TK : Finset V) (v v' : V) {m : ℕ} (z : Fin (m+1)→V) : Prop :=
  PermutationSeparated π b (Fin.cons v z) ∧ PermutationSeparated π b (Fin.cons v' z) ∧
  (∀ i,z i∈if j=false ∧ i.val=2 then TK else T₀) ∧
  P.Adj v (z 0) ∧ P.Adj v' (z 0) ∧
  P.Adj (z (Fin.last m)) (if j then π v else v) ∧
  P.Adj (z (Fin.last m)) (if j then π v' else v') ∧
  ∀ i : Fin m,P.Adj (z i.castSucc) (if j=false ∧ i.val=1 then π (z i.succ) else z i.succ)

theorem markedPathChoice_to_parent {V : Type*} [DecidableEq V]
    (P : SimpleGraph V) (π : Equiv.Perm V) (b r : ℕ) (hr : 1≤r) (j : Bool)
    (T₀ TK : Finset V) (v v' : V) (f : Fin (r+4)→V)
    (hf : MixedGreedyGood P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
      (markedPathChoiceRequests π j (r+4) v v') {v,v'} f) :
    DenseRootMarkedPath P π b j T₀ TK v v' (fun i=>f (pathChoiceOrder (r+2) i)) := by
  let z := fun i=>f (pathChoiceOrder (r+2) i)
  have hz : PermutationSeparated π b z :=
    (permutationSeparated_comp_equiv π b (pathChoiceOrder (r+2)) f).mpr hf.2.1
  have hroot (w : V) (hw : w∈({v,v'}:Finset V)) : PermutationSeparated π b (Fin.cons w z) :=
    permutationSeparated_cons π b w z hz (fun i=>hf.2.2.1 (pathChoiceOrder (r+2) i) w hw)
  have hz0 : z 0=f 0 := by dsimp [z];rw [pathChoiceOrder_zero]
  have hzlast : z (Fin.last (r+3))=f 1 := by dsimp [z];rw [pathChoiceOrder_last]
  have hopen := markedPathChoice_opening P π b r j T₀ TK v v' f hf
  have hclose := markedPathChoice_closing P π b r j T₀ TK v v' f hf
  refine ⟨hroot v (by simp),hroot v' (by simp),?_,?_,?_,?_,?_,?_⟩
  · intro i
    have hv := pathChoiceOrder_val (r+2) i
    have he : (pathChoiceOrder (r+2) i).val=3 ↔ i.val=2 := by
      split_ifs at hv <;> omega
    simpa only [markedPathChoiceClass,he] using hf.1 (pathChoiceOrder (r+2) i)
  · simpa only [← hz0] using hopen.1
  · simpa only [← hz0] using hopen.2
  · simpa only [← hzlast] using hclose.1
  · simpa only [← hzlast] using hclose.2
  · intro i
    by_cases hi0 : i.val=0
    · have hi : i=0 := Fin.ext hi0
      subst i
      have h1 : pathChoiceOrder (r+2) (0:Fin (r+3)).succ=2 := by
        apply Fin.ext
        rw [pathChoiceOrder_val]
        simp [Nat.mod_eq_of_lt (show 2<r+4 by omega)]
      have h0 : pathChoiceOrder (r+2) (0:Fin (r+3)).castSucc=0 := by
        change pathChoiceOrder (r+2) 0=0
        exact pathChoiceOrder_zero _
      simpa only [h0,h1,Fin.val_zero,zero_ne_one,and_false,ite_false] using
        markedPathChoice_first_internal P π b r j T₀ TK v v' f hf
    · by_cases hilast : i=Fin.last (r+2)
      · subst i
        have he : pathChoiceOrder (r+2) (Fin.last (r+2)).castSucc=Fin.last (r+3) := by
          apply Fin.ext
          rw [pathChoiceOrder_val]
          simp only [Fin.val_castSucc,Fin.val_last]
          split_ifs <;> omega
        have he' : pathChoiceOrder (r+2) (Fin.last (r+2)).succ=1 :=
          pathChoiceOrder_last (r+2)
        have hne : (Fin.last (r+2)).val≠1 := by simp
        simpa only [he,he',hne,and_false,ite_false] using
          markedPathChoice_last_internal P π b r hr j T₀ TK v v' f hf
      · have hi : i.val<r+2 := Fin.val_lt_last hilast
        have he : pathChoiceOrder (r+2) i.castSucc=⟨i.val+1,by omega⟩ := by
          apply Fin.ext
          rw [pathChoiceOrder_val]
          simp only [Fin.val_castSucc]
          split_ifs <;> omega
        have he' : pathChoiceOrder (r+2) i.succ=⟨i.val+2,by omega⟩ := by
          apply Fin.ext
          rw [pathChoiceOrder_val]
          simp only [Fin.val_succ]
          split_ifs <;> omega
        have hh := markedPathChoice_internal P π b r j T₀ TK v v' f hf (i.val+2) (by omega) (by omega)
        have hp : (i.val+2)-1=i.val+1 := by omega
        have hmark : i.val+2=3 ↔ i.val=1 := by omega
        by_cases hc : j=false ∧ i.val=1 <;>
          simpa [he,he',markedPathChoiceHead,hmark,hp,hc] using hh

end Oberwolfach
