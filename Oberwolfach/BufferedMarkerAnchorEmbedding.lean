module

public import Oberwolfach.FiniteIndexRangeEmbedding
public import Oberwolfach.PermutationWindows

@[expose] public section
/-! Disjoint buffered source blocks and the original matching-event interval
geometry provide one injective map of every source marker to its interval
label. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def bufferedMarker {X:Type} (c d:ℕ) (ext:Fin (c*d+5)↪X) (j:Fin (d+1)):X:=
  ext ⟨2+c*j.val,by have hj:=j.isLt;have hh:=Nat.mul_le_mul_left c (show j.val≤d by omega);omega⟩

theorem buffered_marker_anchor_embedding
    {X V I:Type} [DecidableEq X] [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (c d:ℕ) (hc:0<c) (ext:∀i:I,Fin (c*d+5)↪X)
    (hsrc:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (π:Equiv.Perm V) (root:I→V)
    (hinj:∀i,Function.Injective (fun j:Fin (d+1)=>(π^j.val) (root i)))
    (htgt:∀i j,i≠j→Disjoint (permutationWindow π 0 d (root i)) (permutationWindow π 0 d (root j))):
    let A:=Finset.univ.image (fun z:I×Fin (d+1)=>bufferedMarker c d (ext z.1) z.2)
    ∃f:{x // x∈A}↪V,
      ∀i (j:Fin (d+1)),f ⟨bufferedMarker c d (ext i) j,Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩⟩=(π^j.val) (root i):=by
  classical
  intro A
  let source:I×Fin (d+1)↪X:=⟨fun z=>bufferedMarker c d (ext z.1) z.2,by
    rintro ⟨i,j⟩ ⟨i',j'⟩ he
    change bufferedMarker c d (ext i) j=bufferedMarker c d (ext i') j' at he
    by_cases hi:i=i'
    · subst i'
      apply Prod.ext
      · rfl
      · apply Fin.ext
        have hh: (⟨2+c*j.val,by have hj:=j.isLt;have hm:=Nat.mul_le_mul_left c (show j.val≤d by omega);omega⟩:Fin (c*d+5))=
          ⟨2+c*j'.val,by have hj:=j'.isLt;have hm:=Nat.mul_le_mul_left c (show j'.val≤d by omega);omega⟩:= (ext i).injective he
        have hv:=congrArg Fin.val hh
        simp only [Fin.val_mk,Prod.snd] at hv
        have hcj:c*j.val=c*j'.val:=by omega
        exact Nat.eq_of_mul_eq_mul_left hc hcj
    · have hleft:bufferedMarker c d (ext i) j∈Finset.univ.image (ext i):=by
        unfold bufferedMarker
        exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
      have hright:bufferedMarker c d (ext i) j∈Finset.univ.image (ext i'):=by
        rw [he]
        unfold bufferedMarker
        exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
      exact False.elim (Finset.disjoint_left.mp (hsrc i i' hi) hleft hright)⟩
  let target:I×Fin (d+1)↪V:=⟨fun z=>(π^z.2.val) (root z.1),by
    rintro ⟨i,j⟩ ⟨i',j'⟩ he
    change (π^j.val) (root i)=(π^j'.val) (root i') at he
    by_cases hi:i=i'
    · subst i'
      exact Prod.ext rfl (hinj i he)
    · have hleft:(π^j.val) (root i)∈permutationWindow π 0 d (root i):=by
        rw [permutationWindow_mem_iff]
        simp only [zero_add, pow_zero, Equiv.refl_apply]
        exact ⟨⟨j.val,by have hj:=j.isLt;omega⟩,rfl⟩
      have hright:(π^j.val) (root i)∈permutationWindow π 0 d (root i'):=by
        rw [he]
        rw [permutationWindow_mem_iff]
        simp only [zero_add, pow_zero, Equiv.refl_apply]
        exact ⟨⟨j'.val,by have hj:=j'.isLt;omega⟩,rfl⟩
      exact False.elim (Finset.disjoint_left.mp (htgt i i' hi) hleft hright)⟩
  obtain ⟨f,hf⟩:=finite_index_range_embedding source target
  exact ⟨f,fun i j=>hf (i,j)⟩
end Oberwolfach
