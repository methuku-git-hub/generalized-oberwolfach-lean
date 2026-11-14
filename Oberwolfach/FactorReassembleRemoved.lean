module

public import Oberwolfach.Definitions

@[expose] public section
/-! Reinsert individually removed factors into a decomposition of the residual
host, preserving their original indices and edge-disjointness. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_reassemble_removed {n q:ℕ}
    (G R:SimpleGraph (Fin n)) (F:Fin q→SimpleGraph (Fin n)) (removed:Finset (Fin q))
    (e:Fin (Fintype.card {i:Fin q // i∉removed})≃{i:Fin q // i∉removed})
    (B:{i:Fin q // i∈removed}→SimpleGraph (Fin n))
    (hR:HasFactorDecomposition R (fun j=>F (e j).val))
    (hBiso:∀i,Nonempty (B i ≃g F i.val))
    (hBdis:∀i x y,(B i).Adj x y→¬R.Adj x y)
    (hBunique:∀i j x y,(B i).Adj x y→(B j).Adj x y→i=j)
    (hcover:∀x y,G.Adj x y↔R.Adj x y ∨ ∃i,(B i).Adj x y):
    HasFactorDecomposition G F:=by
  obtain ⟨A,hApart,hAiso⟩:=hR
  let pieces:Fin q→SimpleGraph (Fin n):=fun i=>if hi:i∈removed then B ⟨i,hi⟩ else A (e.symm ⟨i,hi⟩)
  have hRemain:∀i (hi:i∉removed) x y,(pieces i).Adj x y→R.Adj x y:=by
    intro i hi x y hp
    have hp':(A (e.symm ⟨i,hi⟩)).Adj x y:=by simpa [pieces,hi] using hp
    exact ((hApart x y).1).2 ⟨_,hp'⟩
  refine ⟨pieces,?_,?_⟩
  · intro x y
    constructor
    · constructor
      · intro hg
        rcases (hcover x y).1 hg with hr|⟨i,hi⟩
        · obtain ⟨j,hj⟩:=((hApart x y).1).1 hr
          refine ⟨(e j).val,?_⟩
          simpa [pieces,(e j).property] using hj
        · refine ⟨i.val,?_⟩
          simpa [pieces,i.property] using hi
      · rintro ⟨i,hi⟩
        apply (hcover x y).2
        by_cases him:i∈removed
        · right
          exact ⟨⟨i,him⟩,by simpa [pieces,him] using hi⟩
        · exact Or.inl (hRemain i him x y hi)
    · intro i j hi hj
      by_cases him:i∈removed <;> by_cases hjm:j∈removed
      · have hi':(B ⟨i,him⟩).Adj x y:=by simpa [pieces,him] using hi
        have hj':(B ⟨j,hjm⟩).Adj x y:=by simpa [pieces,hjm] using hj
        exact congrArg Subtype.val (hBunique ⟨i,him⟩ ⟨j,hjm⟩ x y hi' hj')
      · have hi':(B ⟨i,him⟩).Adj x y:=by simpa [pieces,him] using hi
        exact False.elim (hBdis ⟨i,him⟩ x y hi' (hRemain j hjm x y hj))
      · have hj':(B ⟨j,hjm⟩).Adj x y:=by simpa [pieces,hjm] using hj
        exact False.elim (hBdis ⟨j,hjm⟩ x y hj' (hRemain i him x y hi))
      · have hi':(A (e.symm ⟨i,him⟩)).Adj x y:=by simpa [pieces,him] using hi
        have hj':(A (e.symm ⟨j,hjm⟩)).Adj x y:=by simpa [pieces,hjm] using hj
        have heq: e.symm ⟨i,him⟩=e.symm ⟨j,hjm⟩:=(hApart x y).2 _ _ hi' hj'
        exact congrArg Subtype.val (e.symm.injective heq)
  · intro i
    by_cases hi:i∈removed
    · simpa [pieces,hi] using hBiso ⟨i,hi⟩
    · simpa [pieces,hi] using hAiso (e.symm ⟨i,hi⟩)
end Oberwolfach
