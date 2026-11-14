module

public import Oberwolfach.MarkedPathChoices

@[expose] public section

/-! Graph assertions obtained from the endpoint-first greedy choices.
These assertions keep the two distinct root variables and their actual
successor heads visible. No root spoke is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V]

theorem markedPathChoice_opening
    (P : SimpleGraph V) (π : Equiv.Perm V) (b r : ℕ) (j : Bool)
    (T₀ TK : Finset V) (v v' : V) (f : Fin (r+4)→V)
    (hf : MixedGreedyGood P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
      (markedPathChoiceRequests π j (r+4) v v') {v,v'} f) :
    P.Adj v (f 0) ∧ P.Adj v' (f 0) := by
  have h := hf.2.2.2 0
  simpa [markedPathChoiceRequests,markedPathChoiceHead] using h

theorem markedPathChoice_closing
    (P : SimpleGraph V) (π : Equiv.Perm V) (b r : ℕ) (j : Bool)
    (T₀ TK : Finset V) (v v' : V) (f : Fin (r+4)→V)
    (hf : MixedGreedyGood P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
      (markedPathChoiceRequests π j (r+4) v v') {v,v'} f) :
    P.Adj (f 1) (if j then π v else v) ∧ P.Adj (f 1) (if j then π v' else v') := by
  have h := hf.2.2.2 (1:Fin (r+4))
  have hv : (1:Fin (r+4)).val=1 := by simp [Nat.mod_eq_of_lt (show 1<r+4 by omega)]
  simp only [hv] at h
  have h' : P.Adj (if j then π v else v) (f 1) ∧ P.Adj (if j then π v' else v') (f 1) := by
    simpa [markedPathChoiceRequests,markedPathChoiceHead] using h
  exact ⟨h'.1.symm,h'.2.symm⟩

theorem markedPathChoice_first_internal
    (P : SimpleGraph V) (π : Equiv.Perm V) (b r : ℕ) (j : Bool)
    (T₀ TK : Finset V) (v v' : V) (f : Fin (r+4)→V)
    (hf : MixedGreedyGood P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
      (markedPathChoiceRequests π j (r+4) v v') {v,v'} f) : P.Adj (f 0) (f 2) := by
  have h := hf.2.2.2 (2:Fin (r+4))
  have hv : (2:Fin (r+4)).val=2 := by simp [Nat.mod_eq_of_lt (show 2<r+4 by omega)]
  simp only [hv] at h
  have hp : greedyPrefix f (2:Fin (r+4)) ⟨0,by change 0<(2:Fin (r+4)).val;rw [hv];omega⟩=f 0 := by unfold greedyPrefix;congr 1
  simpa [markedPathChoiceRequests,markedPathChoiceHead,hp,Nat.mod_eq_of_lt (show 2<r+4 by omega),greedyPrefix] using h

theorem markedPathChoice_internal
    (P : SimpleGraph V) (π : Equiv.Perm V) (b r : ℕ) (j : Bool)
    (T₀ TK : Finset V) (v v' : V) (f : Fin (r+4)→V)
    (hf : MixedGreedyGood P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
      (markedPathChoiceRequests π j (r+4) v v') {v,v'} f)
    (n : ℕ) (hn : 3≤n) (hnr : n<r+4) :
    P.Adj (f ⟨n-1,by omega⟩) (markedPathChoiceHead π j n (f ⟨n,hnr⟩)) := by
  have h := hf.2.2.2 ⟨n,hnr⟩
  apply h
  change f ⟨n-1,by omega⟩∈markedPathChoiceRequests π j (r+4) v v' n (greedyPrefix f ⟨n,hnr⟩)
  unfold markedPathChoiceRequests
  rw [if_neg (by omega),if_neg (by omega),dif_neg (by omega),dif_pos (by omega)]
  exact Finset.mem_union_left _ (Finset.mem_singleton_self _)

theorem markedPathChoice_last_internal
    (P : SimpleGraph V) (π : Equiv.Perm V) (b r : ℕ) (hr : 1≤r) (j : Bool)
    (T₀ TK : Finset V) (v v' : V) (f : Fin (r+4)→V)
    (hf : MixedGreedyGood P π b (markedPathChoiceClass j T₀ TK) (markedPathChoiceHead π j)
      (markedPathChoiceRequests π j (r+4) v v') {v,v'} f) :
    P.Adj (f (Fin.last (r+3))) (f 1) := by
  have h := hf.2.2.2 (Fin.last (r+3))
  have hp : greedyPrefix f (Fin.last (r+3)) ⟨1,by change 1<r+3;omega⟩=f 1 := by
    unfold greedyPrefix
    congr 1
  have hm : f 1∈markedPathChoiceRequests π j (r+4) v v' (r+3) (greedyPrefix f (Fin.last (r+3))) := by
    unfold markedPathChoiceRequests
    rw [if_neg (by omega),if_neg (by omega),dif_neg (by omega),dif_pos (by omega),if_pos (by omega)]
    rw [hp]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have hh := h (f 1) hm
  have he : markedPathChoiceHead π j (r+3)=Equiv.refl V := by
    unfold markedPathChoiceHead
    rw [if_neg (by rintro ⟨_,he⟩;omega)]
  rw [show (Fin.last (r+3)).val=r+3 from rfl,he] at hh
  exact hh.symm

end Oberwolfach
