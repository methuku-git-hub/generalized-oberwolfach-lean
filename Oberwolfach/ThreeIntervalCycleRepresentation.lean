module

public import Oberwolfach.ThreeBlockCycleOrder

@[expose] public section

/-! A canonical cyclic sequence and its three interval paths have identical
edge occurrences, with no multiplicity from duplicated boundary vertices. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def cycleBlockVertexEquiv (L : Fin 3 → ℕ) (X : Type*) :
    (Fin (∑ i,L i) → X) ≃ ((Σ i,Fin (L i)) → X) where
  toFun v j := v (finSigmaFinEquiv j)
  invFun v j := v (finSigmaFinEquiv.symm j)
  left_inv v := by funext i;simp
  right_inv v := by funext i;simp

def threePathsOfCycle {X : Type*} (L : Fin 3 → ℕ) (hL : ∀ i,0<L i)
    (v : Fin (∑ i,L i) → X) : ∀ i,Fin (L i+1) → X :=
  blockPathsOfVertices L hL (finRotate 3) (cycleBlockVertexEquiv L X v)

theorem threePathsOfCycle_compatible {X : Type*} (L : Fin 3 → ℕ) (hL : ∀ i,0<L i)
    (v : Fin (∑ i,L i) → X) (i : Fin 3) :
    threePathsOfCycle L hL v i (Fin.last (L i))=threePathsOfCycle L hL v (finRotate 3 i) 0 :=
  blockPathsOfVertices_compatible L hL (finRotate 3) _ i

theorem threePathsOfCycle_edge {X : Type*} (L : Fin 3 → ℕ) (hL : ∀ i,0<L i)
    (v : Fin (∑ i,L i) → X) (i : Fin 3) (j : Fin (L i)) :
    threePathsOfCycle L hL v i j.castSucc=v (finSigmaFinEquiv ⟨i,j⟩) ∧
      threePathsOfCycle L hL v i j.succ=v (finRotate (∑ i,L i) (finSigmaFinEquiv ⟨i,j⟩)) := by
  constructor
  · exact Fin.snoc_castSucc (α := fun _ => X)
      ((cycleBlockVertexEquiv L X v) ⟨finRotate 3 i,⟨0,hL (finRotate 3 i)⟩⟩)
      (fun q => (cycleBlockVertexEquiv L X v) ⟨i,q⟩) j
  · rw [threePathsOfCycle,blockPathsOfVertices_next]
    change v (finSigmaFinEquiv (blockNext L hL (finRotate 3) ⟨i,j⟩))=_
    rw [threeBlock_next_position]

theorem threePathsOfCycle_sum {X : Type*} [Fintype X]
    (L : Fin 3 → ℕ) (hL : ∀ i,0<L i)
    (f : (∀ i,Fin (L i+1) → X) → ℝ)
    (hsupp : ∀ p,f p≠0 → ∀ i,p i (Fin.last (L i))=p (finRotate 3 i) 0) :
    (∑ v,f (threePathsOfCycle L hL v))=∑ p,f p := by
  calc
    _ = ∑ v,f (blockPathsOfVertices L hL (finRotate 3) v) :=
      Fintype.sum_equiv (cycleBlockVertexEquiv L X) _ _ (fun _ => rfl)
    _ = _ := blockCycle_sum L hL (finRotate 3) f hsupp

end Oberwolfach
