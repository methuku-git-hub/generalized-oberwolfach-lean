module

public import Oberwolfach.ResourceDecompositions
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Exact finite-set assembly for transformers and absorbers. The host
embedding and the construction of each transformer are separate tasks;
these lemmas preserve all physical edges in the two decompositions. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {E W : Type*} [DecidableEq E] [DecidableEq W]

def IsResourceTransformer (R : W → Finset E) (L L' T : Finset E) : Prop :=
  Disjoint T L ∧ Disjoint T L' ∧
  HasResourceDecomposition R (T∪L) ∧ HasResourceDecomposition R (T∪L')

def IsResourceAbsorber (R : W → Finset E) (L A : Finset E) : Prop :=
  Disjoint A L ∧ HasResourceDecomposition R A ∧ HasResourceDecomposition R (A∪L)

theorem resource_transformer_symm (R : W → Finset E) (L L' T : Finset E)
    (h : IsResourceTransformer R L L' T) : IsResourceTransformer R L' L T :=
  ⟨h.2.1,h.1,h.2.2.2,h.2.2.1⟩

theorem resource_transformer_to_absorber (R : W → Finset E) (L L' T : Finset E)
    (h : IsResourceTransformer R L L' T) (hLL : Disjoint L L')
    (hdec : HasResourceDecomposition R L') : IsResourceAbsorber R L (T∪L') := by
  refine ⟨Finset.disjoint_union_left.mpr ⟨h.1,hLL.symm⟩,h.2.2.2,?_⟩
  have hh := resource_decomposition_union R (T∪L) L' h.2.2.1 hdec
    (Finset.disjoint_union_left.mpr ⟨h.2.1,hLL⟩)
  convert hh using 1 <;> ext e <;> simp only [Finset.mem_union] <;> tauto

theorem resource_absorber_remove_decomposable_part
    (R : W → Finset E) (L K A : Finset E)
    (h : IsResourceAbsorber R (L∪K) A) (hLK : Disjoint L K)
    (hK : HasResourceDecomposition R K) : IsResourceAbsorber R L (A∪K) := by
  have hparts := Finset.disjoint_union_right.mp h.1
  refine ⟨Finset.disjoint_union_left.mpr ⟨hparts.1,hLK.symm⟩,
    resource_decomposition_union R A K h.2.1 hK hparts.2,?_⟩
  convert h.2.2 using 1 <;> ext e <;> simp only [Finset.mem_union] <;> tauto

theorem resource_transformer_compose
    (R : W → Finset E) (L M N T T' : Finset E)
    (hT : IsResourceTransformer R L M T) (hT' : IsResourceTransformer R M N T')
    (hLM : Disjoint L M) (hMN : Disjoint M N) (hTT : Disjoint T T')
    (hTN : Disjoint T N) (hLT : Disjoint L T') :
    IsResourceTransformer R L N (T∪M∪T') := by
  refine ⟨?_,?_,?_,?_⟩
  · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hT.1,hLM.symm⟩,hLT.symm⟩
  · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hTN,hMN⟩,hT'.2.1⟩
  · have hd : Disjoint (T∪L) (T'∪M) := by
      simp only [Finset.disjoint_union_left,Finset.disjoint_union_right]
      exact ⟨⟨hTT,hLT⟩,hT.2.1,hLM⟩
    have hh := resource_decomposition_union R (T∪L) (T'∪M) hT.2.2.1 hT'.2.2.1 hd
    convert hh using 1 <;> ext e <;> simp only [Finset.mem_union] <;> tauto
  · have hd : Disjoint (T∪M) (T'∪N) := by
      simp only [Finset.disjoint_union_left,Finset.disjoint_union_right]
      exact ⟨⟨hTT,hT'.1.symm⟩,hTN,hMN⟩
    have hh := resource_decomposition_union R (T∪M) (T'∪N) hT.2.2.2 hT'.2.2.2 hd
    convert hh using 1 <;> ext e <;> simp only [Finset.mem_union] <;> tauto

theorem resource_transformer_of_indicator_identity
    (R : W → Finset E) (L L' A B : Finset E)
    (hA : HasResourceDecomposition R A) (hB : HasResourceDecomposition R B)
    (hL : L ⊆ A) (hL' : L' ⊆ B) (hLB : Disjoint L B) (hL'A : Disjoint L' A)
    (hid : ∀ e, (if e∈A then (1:ℤ) else 0)-(if e∈B then 1 else 0)=
      (if e∈L then 1 else 0)-(if e∈L' then 1 else 0)) :
    A\L=B\L' ∧ IsResourceTransformer R L L' (A\L) := by
  have heq : A\L=B\L' := by
    ext e
    have hh := hid e
    by_cases ha : e∈A <;> by_cases hb : e∈B <;> by_cases hl : e∈L <;> by_cases hl' : e∈L' <;>
      simp only [ha,hb,hl,hl',ite_true,ite_false] at hh <;>
      simp only [Finset.mem_sdiff,ha,hb,hl,hl',not_true_eq_false,not_false_eq_true,and_true,and_false,true_and,false_and] <;> omega
  have hAL : (A\L)∪L=A := Finset.sdiff_union_of_subset hL
  have hBL : (B\L')∪L'=B := Finset.sdiff_union_of_subset hL'
  refine ⟨heq,Finset.disjoint_left.mpr (fun e he hl => (Finset.mem_sdiff.mp he).2 hl),?_,?_,?_⟩
  · exact hL'A.symm.mono_left Finset.sdiff_subset
  · rwa [hAL]
  · rwa [heq,hBL]

end Oberwolfach
