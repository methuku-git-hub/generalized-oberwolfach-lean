module

public import Oberwolfach.BufferedPathInteriorCompletion

@[expose] public section
/-! Exact cardinalities of the strict path interiors deleted in the
long-factor remainder. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def strictPathIndex (n:ℕ) : Fin (n-1) ↪ Fin (n+1) where
  toFun j:=⟨j.val+1,by omega⟩
  inj' := by intro i j h;apply Fin.ext;have hh:i.val+1=j.val+1:=congrArg Fin.val h;omega

theorem strict_path_index_card (n:ℕ) :
    (Finset.univ.filter (fun p:Fin (n+1)=>0<p.val ∧ p.val<n)).card=n-1 := by
  classical
  have heq:(Finset.univ.filter (fun p:Fin (n+1)=>0<p.val ∧ p.val<n))=
      Finset.univ.image (strictPathIndex n):=by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro hp
      let j:Fin (n-1):=⟨p.val-1,by omega⟩
      refine ⟨j,?_⟩
      apply Fin.ext
      change (p.val-1)+1=p.val
      omega
    · rintro ⟨j,rfl⟩
      change 0<j.val+1 ∧ j.val+1<n
      have hj:j.val<n-1:=j.isLt
      omega
  rw [heq,Finset.card_image_of_injective _ (strictPathIndex n).injective]
  simp

theorem buffered_strict_interior_card
    {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) :
    (bufferedPathStrictInterior n inner).card=∑i,(n i-1) := by
  classical
  have hsubset (i:I):(Finset.univ.filter (fun p:Fin (n i+1)=>0<p.val ∧ p.val<n i)).image (inner i)⊆
      Finset.univ.image (ext i):=by
    intro x hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    rw [hinner i k]
    exact Finset.mem_image.mpr ⟨⟨k.val+2,by omega⟩,Finset.mem_univ _,rfl⟩
  unfold bufferedPathStrictInterior
  rw [Finset.card_biUnion (by
    intro i hi j hj hij
    exact (hdis i j hij).mono (hsubset i) (hsubset j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.card_image_of_injective _ (inner i).injective,strict_path_index_card]

theorem buffered_strict_interior_complement_card
    {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) :
    (Finset.univ\bufferedPathStrictInterior n inner).card=Fintype.card V-∑i,(n i-1) := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    buffered_strict_interior_card n ext inner hinner hdis]
end Oberwolfach
