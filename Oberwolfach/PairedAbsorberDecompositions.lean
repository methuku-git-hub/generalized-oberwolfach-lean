module

public import Oberwolfach.ResourceTransformers

@[expose] public section

/-! The two exact factors in a paired absorber. Cycle identifiers may
come from ordinary, directed or typed families; only their actual vertex
sets enter the partition argument. -/
set_option autoImplicit false
set_option maxHeartbeats 2300000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V C : Type*} [Fintype I] [DecidableEq I] [DecidableEq V] [DecidableEq C]

theorem paired_absorber_decompositions (R : C → Finset V) (x y : I → V) (P : I → Finset V)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j))
    (hPX : Disjoint (Finset.univ.biUnion P) (Finset.univ.image x))
    (hPY : Disjoint (Finset.univ.biUnion P) (Finset.univ.image y))
    (hXY : Disjoint (Finset.univ.image x) (Finset.univ.image y))
    (base : C) (zero one : I → C)
    (hbase : R base=Finset.univ.image y)
    (hzero : ∀ i,R (zero i)=P i∪{y i}) (hone : ∀ i,R (one i)=P i∪{x i}) :
    IsResourceAbsorber R (Finset.univ.image x)
      ((Finset.univ.biUnion P)∪Finset.univ.image y) := by
  have hpair (f : I → V) (hf : Function.Injective f)
      (hPf : Disjoint (Finset.univ.biUnion P) (Finset.univ.image f))
      (D : I → C) (hD : ∀ i,R (D i)=P i∪{f i}) :
      HasResourceDecomposition R ((Finset.univ.biUnion P)∪Finset.univ.image f) := by
    have hd := resource_decomposition_biUnion R (fun i => R (D i)) Finset.univ
      (fun i _ => resource_decomposition_singleton R (D i)) (by
        intro i _ j _ hij
        rw [hD,hD]
        apply Finset.disjoint_union_left.mpr
        constructor
        · apply Finset.disjoint_union_right.mpr
          exact ⟨hP i j hij,hPf.mono (resource_subset_union P Finset.univ i (Finset.mem_univ _))
            (Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))⟩
        · apply Finset.disjoint_union_right.mpr
          constructor
          · exact hPf.symm.mono (Finset.singleton_subset_iff.mpr (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
              (resource_subset_union P Finset.univ j (Finset.mem_univ _))
          · simp only [Finset.disjoint_singleton_left,Finset.mem_singleton]
            exact fun he => hij (hf he))
    have heq : Finset.univ.biUnion (fun i => R (D i))=(Finset.univ.biUnion P)∪Finset.univ.image f := by
      ext v
      simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,hD,Finset.mem_union,Finset.mem_singleton,
        Finset.mem_image]
      constructor
      · rintro ⟨i,hi | hi⟩
        · exact Or.inl ⟨i,hi⟩
        · exact Or.inr ⟨i,hi.symm⟩
      · rintro (⟨i,hi⟩ | ⟨i,hi⟩)
        · exact ⟨i,Or.inl hi⟩
        · exact ⟨i,Or.inr hi.symm⟩
    rwa [heq] at hd
  refine ⟨Finset.disjoint_union_left.mpr ⟨hPX,hXY.symm⟩,hpair y hy hPY zero hzero,?_⟩
  have hb : HasResourceDecomposition R (Finset.univ.image y) := by
    rw [← hbase];exact resource_decomposition_singleton R base
  have hd := resource_decomposition_union R ((Finset.univ.biUnion P)∪Finset.univ.image x)
    (Finset.univ.image y) (hpair x hx hPX one hone) hb
    (Finset.disjoint_union_left.mpr ⟨hPY,hXY⟩)
  convert hd using 1 <;> ext v <;> simp only [Finset.mem_union] <;> tauto

theorem paired_absorber_free_card (c : ℕ) (hc : 1 ≤ c) (y : Fin c → V)
    (hy : Function.Injective y) (P : Fin c → Finset V)
    (hP : ∀ i j,i≠j → Disjoint (P i) (P j)) (hcard : ∀ i,(P i).card=c-1)
    (hPY : Disjoint (Finset.univ.biUnion P) (Finset.univ.image y)) :
    ((Finset.univ.biUnion P)∪Finset.univ.image y).card=c^2 := by
  rw [Finset.card_union_of_disjoint hPY,Finset.card_biUnion
    (by intro i _ j _ hij;exact hP i j hij),Finset.card_image_of_injective _ hy]
  simp only [hcard,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have he : c-1+1=c := by omega
  nlinarith

end Oberwolfach
