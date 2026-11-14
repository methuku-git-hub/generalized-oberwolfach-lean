module

public import Oberwolfach.BufferedStrictInteriorCardinality

@[expose] public section
/-! The equal-length case used for the final reserved path family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem uniform_buffered_strict_interior_card
    {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (L:ℕ) (ext:∀i:I,Fin (L+5)↪V) (inner:∀i:I,Fin (L+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) :
    (bufferedPathStrictInterior (fun _ : I=>L) inner).card=Fintype.card I*(L-1) := by
  rw [buffered_strict_interior_card (fun _ : I=>L) ext inner hinner hdis]
  simp

theorem uniform_buffered_strict_interior_complement_card
    {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (L:ℕ) (ext:∀i:I,Fin (L+5)↪V) (inner:∀i:I,Fin (L+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) :
    (Finset.univ\bufferedPathStrictInterior (fun _ : I=>L) inner).card=
      Fintype.card V-Fintype.card I*(L-1) := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    uniform_buffered_strict_interior_card L ext inner hinner hdis]
end Oberwolfach
