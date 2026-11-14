module

public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Exact domain and complement counts for disjoint buffered path interiors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
open scoped BigOperators

theorem buffered_path_interior_domain_card
    {V I:Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I):
    (A.biUnion (fun i=>Finset.univ.image (inner i))).card=∑i∈A,(n i+1) := by
  classical
  have hsubset (i:I):Finset.univ.image (inner i)⊆Finset.univ.image (ext i):=by
    intro x hx
    obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hx
    rw [hinner i k]
    exact Finset.mem_image.mpr ⟨⟨k.val+2,by omega⟩,Finset.mem_univ _,rfl⟩
  rw [Finset.card_biUnion (by
    intro i hi j hj hij
    exact (hdis i j hij).mono (hsubset i) (hsubset j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.card_image_of_injective _ (inner i).injective]
  simp

theorem buffered_path_interior_complement_card
    {V I:Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I):
    (Finset.univ\A.biUnion (fun i=>Finset.univ.image (inner i))).card=
      Fintype.card V-∑i∈A,(n i+1):=by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    buffered_path_interior_domain_card n ext inner hinner hdis A]
end Oberwolfach
