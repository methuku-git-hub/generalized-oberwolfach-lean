module

public import Oberwolfach.ActualResidualDataFromFamilies

@[expose] public section
/-! The original two path index types are equivalent to the selected index
subtypes in the assembled residual data. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def firstSumIndexEquiv {A B:Type} [Fintype A] [DecidableEq A] [DecidableEq B]:
    A≃{i // i∈firstSumIndices (A:=A) (B:=B)}:=
  Equiv.ofBijective (fun a=>⟨Sum.inl a,Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩⟩) (by
    constructor
    · intro a b h
      exact Sum.inl.inj (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hx
      refine ⟨a,?_⟩
      exact Subtype.ext ha)

def secondSumIndexEquiv {A B:Type} [Fintype B] [DecidableEq A] [DecidableEq B]:
    B≃{i // i∈secondSumIndices (A:=A) (B:=B)}:=
  Equiv.ofBijective (fun b=>⟨Sum.inr b,Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩⟩) (by
    constructor
    · intro a b h
      exact Sum.inr.inj (congrArg Subtype.val h)
    · rintro ⟨x,hx⟩
      obtain ⟨b,_,hb⟩:=Finset.mem_image.mp hx
      refine ⟨b,?_⟩
      exact Subtype.ext hb)

@[simp] theorem first_sum_index_equiv_val {A B:Type} [Fintype A] [DecidableEq A] [DecidableEq B] (a:A):
    (firstSumIndexEquiv (B:=B) a).val=Sum.inl a:=rfl
@[simp] theorem second_sum_index_equiv_val {A B:Type} [Fintype B] [DecidableEq A] [DecidableEq B] (b:B):
    (secondSumIndexEquiv (A:=A) b).val=Sum.inr b:=rfl
end Oberwolfach
