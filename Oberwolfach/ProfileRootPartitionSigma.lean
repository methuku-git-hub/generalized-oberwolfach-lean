module

public import Oberwolfach.ProfileRootCounts
public import Oberwolfach.ProfileRootPartition
public import Oberwolfach.SigmaClassCounts

@[expose] public section

/-! Partition a later leftover with the required class proportions into
actual admissible root choices; the partition may be chosen after the
reservoir has been fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I]
    {V : I → Type*} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]

theorem profile_root_partition_sigma (a : I → ℕ) (W : Finset (Σ i,V i)) (q : ℕ)
    (hW : ∀ i,(Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈W)).card=a i*q) :
    ∃ σ : Fin q → ∀ i,FixedSubset (V i) (a i),
      Finset.univ.biUnion (fun j => profileRootSet (σ j))=W ∧
      ∀ j k,j≠k → Disjoint (profileRootSet (σ j)) (profileRootSet (σ k)) := by
  let A (i : I) := W.filter (fun v => v.1=i)
  have hA (i : I) : (A i).card=a i*q := (sigma_finset_class_card W i).trans (hW i)
  have hAA : ∀ i j,i≠j → Disjoint (A i) (A j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact hij ((Finset.mem_filter.mp hv).2.symm.trans (Finset.mem_filter.mp hw).2)
  obtain ⟨X,hU,hXX,hX⟩ := profile_root_partition A a q hA hAA
  have hAW : Finset.univ.biUnion A=W := by
    ext v
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hi⟩;exact (Finset.mem_filter.mp hi).1
    · intro hv;exact ⟨v.1,Finset.mem_filter.mpr ⟨hv,rfl⟩⟩
  rw [hAW] at hU
  have hXW (j : Fin q) : X j⊆W := by
    intro v hv
    rw [← hU]
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hv⟩
  have hp (j : Fin q) (i : I) :
      (Finset.univ.filter (fun v : V i => (⟨i,v⟩ : Σ i,V i)∈X j)).card=a i := by
    rw [← sigma_finset_class_card]
    have he : (X j).filter (fun v => v.1=i)=X j∩A i := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_inter,A]
      constructor
      · rintro ⟨hv,hi⟩;exact ⟨hv,hXW j hv,hi⟩
      · rintro ⟨hv,hw,hi⟩;exact ⟨hv,hi⟩
    rw [he,hX]
  choose σ hσ using fun j => exists_profile_root_of_class_sizes a (X j) (hp j)
  refine ⟨σ,?_,?_⟩
  · simpa only [hσ] using hU
  · intro j k hjk
    simpa only [hσ] using hXX j k hjk

end Oberwolfach
