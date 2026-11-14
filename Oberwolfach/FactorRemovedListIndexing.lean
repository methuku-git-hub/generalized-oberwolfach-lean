module

public import Oberwolfach.FactorReassembleRemoved
public import Mathlib.Data.List.NodupEquivFin

@[expose] public section
/-! Index the sequentially removed graph copies by the original factor indices,
including edge-disjointness and coverage of the complete output list. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_removed_list_indexing {n q:ℕ}
    (F:Fin q→SimpleGraph (Fin n)) (removed:Finset (Fin q))
    (pieces:List (SimpleGraph (Fin n)))
    (hRel:List.Forall₂ (fun H A=>Nonempty (H ≃g A) ∧ H.IsRegularOfDegree 2)
      pieces (removed.toList.map F))
    (hPair:pieces.Pairwise (fun H J=>∀x y,H.Adj x y→¬J.Adj x y)):
    ∃B:{i:Fin q // i∈removed}→SimpleGraph (Fin n),
      (∀i,Nonempty (B i ≃g F i.val)) ∧
      (∀i,B i∈pieces) ∧
      (∀i j x y,(B i).Adj x y→(B j).Adj x y→i=j) ∧
      (∀H∈pieces,∃i,B i=H):=by
  let L:=removed.toList
  let E:Fin L.length≃{i:Fin q // i∈removed}:=
    (List.Nodup.getEquiv L (by simpa [L] using removed.nodup_toList)).trans (Equiv.subtypeEquivRight (by intro i; simp [L]))
  have hlen:pieces.length=L.length:=by simpa [L] using hRel.length_eq
  let index (i:{i:Fin q // i∈removed}):Fin pieces.length:=
    ⟨(E.symm i).val,by simpa [hlen] using (E.symm i).isLt⟩
  let B (i:{i:Fin q // i∈removed}):SimpleGraph (Fin n):=pieces.get (index i)
  have hget (i:{i:Fin q // i∈removed}):L.get (E.symm i)=i.val:=by
    have h:=congrArg Subtype.val (E.apply_symm_apply i)
    simpa [E] using h
  have hinj:Function.Injective index:=by
    intro i j hij
    apply E.symm.injective
    apply Fin.ext
    have hv:(index i).val=(index j).val:=congrArg (fun x:Fin pieces.length=>x.val) hij
    exact hv
  refine ⟨B,?_,?_,?_,?_⟩
  · intro i
    have hp:(E.symm i).val<pieces.length:=(index i).isLt
    have hL:(E.symm i).val<(removed.toList.map F).length:=by simpa [L] using (E.symm i).isLt
    have h:=hRel.get hp hL
    have hIso:Nonempty (pieces.get (index i) ≃g F (L.get (E.symm i))):=by
      simpa [L,index] using h.1
    rw [hget i] at hIso
    exact hIso
  · intro i
    exact List.get_mem _ _
  · intro i j x y hi hj
    by_contra hne
    have hidx:index i≠index j:=fun h=>hne (hinj h)
    rcases lt_or_gt_of_ne hidx with hlt|hgt
    · exact (hPair.rel_get_of_lt hlt) x y hi hj
    · exact (hPair.rel_get_of_lt hgt) x y hj hi
  · intro H hH
    obtain ⟨k,hk⟩:=List.mem_iff_get.mp hH
    let kL:Fin L.length:=⟨k.val,by simpa [←hlen] using k.isLt⟩
    refine ⟨E kL,?_⟩
    have heq:index (E kL)=k:=by
      apply Fin.ext
      simp [index,kL]
    change pieces.get (index (E kL))=H
    rw [heq,hk]
end Oberwolfach
