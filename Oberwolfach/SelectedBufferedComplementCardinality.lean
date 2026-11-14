module

public import Oberwolfach.SelectedBufferedPathCardinality

@[expose] public section
/-! The exact source size after deleting interiors of the final paths. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_uniform_buffered_complement_card
    {V I:Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (S:Finset I) (L:ℕ) (ext:∀i:I,Fin (L+5)↪V) (inner:∀i:I,Fin (L+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j))) :
    (Finset.univ\bufferedPathStrictInterior (bufferedSelectedLengths S (fun _=>L))
      (bufferedSelectedPaths S (fun _=>L) inner)).card=Fintype.card V-S.card*(L-1) := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
    selected_uniform_buffered_strict_interior_card S L ext inner hinner hdis]
end Oberwolfach
