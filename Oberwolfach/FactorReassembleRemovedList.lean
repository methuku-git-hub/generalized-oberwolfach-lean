module

public import Oberwolfach.FactorRemovedListIndexing

@[expose] public section
/-! The sequential small-class removal output can be reinserted after the
remaining factors decompose the residual graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_reassemble_removed_list {n q:ℕ}
    (G R:SimpleGraph (Fin n)) (F:Fin q→SimpleGraph (Fin n)) (removed:Finset (Fin q))
    (e:Fin (Fintype.card {i:Fin q // i∉removed})≃{i:Fin q // i∉removed})
    (pieces:List (SimpleGraph (Fin n)))
    (hRel:List.Forall₂ (fun H A=>Nonempty (H ≃g A) ∧ H.IsRegularOfDegree 2)
      pieces (removed.toList.map F))
    (hPair:pieces.Pairwise (fun H J=>∀x y,H.Adj x y→¬J.Adj x y))
    (hDis:∀H∈pieces,∀x y,H.Adj x y→¬R.Adj x y)
    (hcover:∀x y,G.Adj x y↔R.Adj x y ∨ ∃H∈pieces,H.Adj x y)
    (hR:HasFactorDecomposition R (fun j=>F (e j).val)):
    HasFactorDecomposition G F:=by
  obtain ⟨B,hIso,hMem,hUnique,hAll⟩:=factor_removed_list_indexing F removed pieces hRel hPair
  apply factor_reassemble_removed G R F removed e B hR hIso
  · intro i x y hi
    exact hDis (B i) (hMem i) x y hi
  · exact hUnique
  · intro x y
    rw [hcover x y]
    constructor
    · rintro (hr|⟨H,hH,hxy⟩)
      · exact Or.inl hr
      · obtain ⟨i,hi⟩:=hAll H hH
        exact Or.inr ⟨i,hi ▸ hxy⟩
    · rintro (hr|⟨i,hi⟩)
      · exact Or.inl hr
      · exact Or.inr ⟨B i,hMem i,hi⟩
end Oberwolfach
