module

public import Oberwolfach.FreshMarkedTransformerHubs

@[expose] public section

/-! Exact ordinary and marked spoke requests of two paired cycles, with
four optional ordinary attachment labels. Shared vertices at the same
position have the same type. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E K:Type} [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}

 def markedPairOrdinaryRows (C D:MarkedCycleTuple tail head ktail khead m π b) (T:Finset V):Finset V:=
  (Finset.univ.image (fun i:Fin m=>C.val i.succ))∪
    (Finset.univ.image (fun i:Fin m=>D.val i.succ))∪T

 def markedPairMarkedRows (C D:MarkedCycleTuple tail head ktail khead m π b):Finset V:=
  {C.val 0,D.val 0}

 theorem marked_pair_hub_rows_disjoint (C D:MarkedCycleTuple tail head ktail khead m π b) (T:Finset V)
    (halign:∀ i j,C.val i=D.val j→i=j)
    (hT:∀ x∈T,x≠C.val 0∧x≠D.val 0):
    Disjoint (markedPairOrdinaryRows C D T) (markedPairMarkedRows C D):=by
  have hC:=permutationSeparated_injective π b C.val C.property.1
  have hD:=permutationSeparated_injective π b D.val D.property.1
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [markedPairOrdinaryRows,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hx
  simp only [markedPairMarkedRows,Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hx with (⟨i,hi⟩|⟨i,hi⟩)|hx
  · rcases hy with hy|hy
    · exact Fin.succ_ne_zero i (hC (hi.trans hy))
    · exact Fin.succ_ne_zero i (halign _ _ (hi.trans hy))
  · rcases hy with hy|hy
    · exact Fin.succ_ne_zero i (halign _ _ (hi.trans hy).symm).symm
    · exact Fin.succ_ne_zero i (hD (hi.trans hy))
  · exact hy.elim (hT x hx).1 (hT x hx).2

 theorem marked_pair_hub_rows_subset (C D:MarkedCycleTuple tail head ktail khead m π b) (T:Finset V):
    markedPairOrdinaryRows C D T∪markedPairMarkedRows C D⊆
      (Finset.univ.image C.val∪Finset.univ.image D.val)∪T:=by
  intro x hx
  rcases Finset.mem_union.mp hx with hx|hx
  · simp only [markedPairOrdinaryRows,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hx
    rcases hx with (⟨i,hi⟩|⟨i,hi⟩)|hx
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i.succ,Finset.mem_univ _,hi⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i.succ,Finset.mem_univ _,hi⟩))
    · exact Finset.mem_union_right _ hx
  · simp only [markedPairMarkedRows,Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩))

 theorem marked_pair_hub_rows_card (C D:MarkedCycleTuple tail head ktail khead m π b) (T:Finset V)
    (halign:∀ i j,C.val i=D.val j→i=j)
    (hT:∀ x∈T,x≠C.val 0∧x≠D.val 0)
    (hsize:(Finset.univ.image C.val∪Finset.univ.image D.val).card≤m+3) (hTcard:T.card≤4):
    (markedPairOrdinaryRows C D T).card+(markedPairMarkedRows C D).card≤(m+1)+6:=by
  rw [← Finset.card_union_of_disjoint (marked_pair_hub_rows_disjoint C D T halign hT)]
  have hsub:=Finset.card_le_card (marked_pair_hub_rows_subset C D T)
  have hu:=Finset.card_union_le (Finset.univ.image C.val∪Finset.univ.image D.val) T
  omega

 theorem marked_pair_hub_rows_contain (C D:MarkedCycleTuple tail head ktail khead m π b) (T:Finset V):
    (∀ i:Fin m,C.val i.succ∈markedPairOrdinaryRows C D T)∧
    (∀ i:Fin m,D.val i.succ∈markedPairOrdinaryRows C D T)∧
    C.val 0∈markedPairMarkedRows C D∧D.val 0∈markedPairMarkedRows C D∧T⊆markedPairOrdinaryRows C D T:=by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i;exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  · intro i;exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  · simp [markedPairMarkedRows]
  · simp [markedPairMarkedRows]
  · exact Finset.subset_union_right

end Oberwolfach
