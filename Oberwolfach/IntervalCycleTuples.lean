module

public import Oberwolfach.TransitionPathWeights
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! Compatible interval paths and one vertex in each of their positions are
in bijection. Boundary vertices are represented once, not once per interval. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

def blockPathsOfVertices {I X : Type*} (L : I → ℕ) (hL : ∀ i, 0<L i)
    (σ : I → I) (v : (Σ i,Fin (L i)) → X) (i : I) : Fin (L i+1) → X :=
  Fin.snoc (fun j => v ⟨i,j⟩) (v ⟨σ i,⟨0,hL (σ i)⟩⟩)

def blockPathVertices {I X : Type*} (L : I → ℕ) (p : ∀ i,Fin (L i+1) → X) :
    (Σ i,Fin (L i)) → X := fun j => p j.1 j.2.castSucc

theorem blockPathsOfVertices_first {I X : Type*} (L : I → ℕ) (hL : ∀ i, 0<L i)
    (σ : I → I) (v : (Σ i,Fin (L i)) → X) (i : I) :
    blockPathsOfVertices L hL σ v i 0=v ⟨i,⟨0,hL i⟩⟩ := by
  exact Fin.snoc_castSucc _ _ ⟨0,hL i⟩

theorem blockPathsOfVertices_last {I X : Type*} (L : I → ℕ) (hL : ∀ i, 0<L i)
    (σ : I → I) (v : (Σ i,Fin (L i)) → X) (i : I) :
    blockPathsOfVertices L hL σ v i (Fin.last (L i))=v ⟨σ i,⟨0,hL (σ i)⟩⟩ := by
  exact Fin.snoc_last _ _

theorem blockPathsOfVertices_compatible {I X : Type*} (L : I → ℕ) (hL : ∀ i, 0<L i)
    (σ : I → I) (v : (Σ i,Fin (L i)) → X) (i : I) :
    blockPathsOfVertices L hL σ v i (Fin.last (L i))=blockPathsOfVertices L hL σ v (σ i) 0 := by
  rw [blockPathsOfVertices_last,blockPathsOfVertices_first]

theorem blockPathVertices_left_inverse {I X : Type*} (L : I → ℕ) (hL : ∀ i, 0<L i)
    (σ : I → I) (v : (Σ i,Fin (L i)) → X) :
    blockPathVertices L (blockPathsOfVertices L hL σ v)=v := by
  funext j
  rcases j with ⟨i,j⟩
  exact Fin.snoc_castSucc (α := fun _ => X) (v ⟨σ i,⟨0,hL (σ i)⟩⟩) (fun q => v ⟨i,q⟩) j

theorem blockPathVertices_right_inverse {I X : Type*} (L : I → ℕ) (hL : ∀ i, 0<L i)
    (σ : I → I) (p : ∀ i,Fin (L i+1) → X)
    (hp : ∀ i,p i (Fin.last (L i))=p (σ i) 0) :
    blockPathsOfVertices L hL σ (blockPathVertices L p)=p := by
  funext i
  change Fin.snoc (Fin.init (p i)) (p (σ i) 0)=p i
  rw [← hp i]
  exact Fin.snoc_init_self _

def blockCycleTupleEquiv {I X : Type*} (L : I → ℕ) (hL : ∀ i, 0<L i) (σ : I → I) :
    ((Σ i,Fin (L i)) → X) ≃ {p : ∀ i,Fin (L i+1) → X // ∀ i,p i (Fin.last (L i))=p (σ i) 0} where
  toFun v := ⟨blockPathsOfVertices L hL σ v,blockPathsOfVertices_compatible L hL σ v⟩
  invFun p := blockPathVertices L p.val
  left_inv := blockPathVertices_left_inverse L hL σ
  right_inv p := Subtype.ext (blockPathVertices_right_inverse L hL σ p.val p.property)

theorem blockCycle_sum {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]
    (L : I → ℕ) (hL : ∀ i, 0<L i) (σ : I → I)
    (f : (∀ i,Fin (L i+1) → X) → ℝ)
    (hsupp : ∀ p,f p≠0 → ∀ i,p i (Fin.last (L i))=p (σ i) 0) :
    (∑ v,f (blockPathsOfVertices L hL σ v))=∑ p,f p := by
  classical
  apply Fintype.sum_of_injective (blockPathsOfVertices L hL σ)
    (Function.LeftInverse.injective (blockPathVertices_left_inverse L hL σ)) _ f
  · intro p hp
    by_contra hzero
    exact hp ⟨blockPathVertices L p,blockPathVertices_right_inverse L hL σ p (hsupp p hzero)⟩
  · intro v
    rfl

end Oberwolfach
