module

public import Oberwolfach.IntervalCycleTuples
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

/-! Concatenation of three positive interval lengths preserves cyclic order. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def threeBlockStart (L : Fin 3 → ℕ) : Fin 3 → ℕ := ![0,L 0,L 0+L 1]

def blockNext {I : Type*} (L : I → ℕ) (hL : ∀ i,0<L i) (σ : I → I)
    (j : Σ i,Fin (L i)) : Σ i,Fin (L i) :=
  if h : j.2.val+1<L j.1 then ⟨j.1,⟨j.2.val+1,h⟩⟩ else ⟨σ j.1,⟨0,hL (σ j.1)⟩⟩

theorem threeBlockPosition_val (L : Fin 3 → ℕ) (j : Σ i,Fin (L i)) :
    (finSigmaFinEquiv j).val=threeBlockStart L j.1+j.2.val := by
  rw [finSigmaFinEquiv_apply]
  rcases j with ⟨i,j⟩
  fin_cases i <;> simp [threeBlockStart,Fin.sum_univ_succ]

theorem threeBlock_total_pos (L : Fin 3 → ℕ) (hL : ∀ i,0<L i) : 0<∑ i,L i := by
  have := hL 0
  simp only [Fin.sum_univ_succ] at *
  omega

theorem finRotate_val_if {n : ℕ} (i : Fin n) :
    (finRotate n i).val=if i.val+1<n then i.val+1 else 0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  rw [finRotate_apply,Fin.val_add_one]
  split_ifs with h h' h' <;> simp_all [Fin.ext_iff] <;> omega

theorem threeBlock_next_position (L : Fin 3 → ℕ) (hL : ∀ i,0<L i)
    (j : Σ i,Fin (L i)) :
    finSigmaFinEquiv (blockNext L hL (finRotate 3) j)=finRotate (∑ i,L i) (finSigmaFinEquiv j) := by
  rcases j with ⟨i,j⟩
  have h0 := hL 0
  have h1 := hL 1
  have h2 := hL 2
  by_cases hj : j.val+1<L i
  · have he : blockNext L hL (finRotate 3) ⟨i,j⟩=⟨i,⟨j.val+1,hj⟩⟩ := dite_eq_left hj
    rw [he]
    apply Fin.ext
    rw [threeBlockPosition_val,finRotate_val_if,threeBlockPosition_val]
    have hb (q : Fin 3) : threeBlockStart L q+L q ≤ ∑ i,L i := by
      fin_cases q <;> simp [threeBlockStart,Fin.sum_univ_succ] <;> omega
    have hh : threeBlockStart L i+j.val+1<∑ i,L i := by have := hb i; omega
    rw [ite_eq_left hh]
    rfl
  · have he : blockNext L hL (finRotate 3) ⟨i,j⟩=⟨finRotate 3 i,⟨0,hL (finRotate 3 i)⟩⟩ := dite_eq_right hj
    rw [he]
    apply Fin.ext
    rw [threeBlockPosition_val,finRotate_val_if,threeBlockPosition_val]
    have hjlast : j.val+1=L i := by omega
    fin_cases i <;> norm_num [threeBlockStart,finRotate_apply,Fin.sum_univ_succ] at * <;>
      (try split_ifs) <;> omega

theorem blockPathsOfVertices_next {I X : Type*} (L : I → ℕ) (hL : ∀ i,0<L i)
    (σ : I → I) (v : (Σ i,Fin (L i)) → X) (i : I) (j : Fin (L i)) :
    blockPathsOfVertices L hL σ v i j.succ=v (blockNext L hL σ ⟨i,j⟩) := by
  by_cases hj : j.val+1<L i
  · have he : j.succ=(⟨j.val+1,hj⟩ : Fin (L i)).castSucc := by apply Fin.ext;rfl
    rw [he]
    simp only [blockPathsOfVertices,Fin.snoc_castSucc,blockNext,dite_eq_left hj]
  · have he : j.succ=Fin.last (L i) := by apply Fin.ext;dsimp;omega
    rw [he,blockPathsOfVertices_last]
    simp only [blockNext,dite_eq_right hj]

end Oberwolfach
