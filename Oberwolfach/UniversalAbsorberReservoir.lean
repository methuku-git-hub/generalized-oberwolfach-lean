module

public import Oberwolfach.AbsorberReservoirAssembly

@[expose] public section

/-! One fixed absorber reservoir works for every later disjoint union
of an admissible bounded number of root sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I C E W : Type*} [Fintype C] [DecidableEq I] [DecidableEq C]
    [DecidableEq E] [DecidableEq W]

theorem biUnion_finset_subtype {D : Type*} [DecidableEq D] (S : Finset D) (A : D → Finset E) :
    Finset.univ.biUnion (fun j : S => A j.val)=S.biUnion A := by
  ext e
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj⟩;exact ⟨j.val,j.property,hj⟩
  · rintro ⟨j,hj,he⟩;exact ⟨⟨j,hj⟩,he⟩

theorem universal_absorber_reservoir (R : W → Finset E) (X : I → Finset E)
    (A : C → Finset E) (S : Finset C) (b : ℝ)
    (hAA : ∀ i∈S,∀ j∈S,i≠j → Disjoint (A i) (A j))
    (hA : ∀ j∈S,HasResourceDecomposition R (A j))
    (hchoices : ∀ i,b ≤ ((S.filter (fun j => HasResourceDecomposition R (A j∪X i))).card:ℝ)) :
    ∀ M : Finset I,(M.card:ℝ) ≤ b →
      (∀ i∈M,∀ j∈M,i≠j → Disjoint (X i) (X j)) →
      Disjoint (M.biUnion X) (S.biUnion A) →
      IsResourceAbsorber R (M.biUnion X) (S.biUnion A) := by
  intro M hM hXX hXA
  let P (i : M) (j : C) := j∈S ∧ HasResourceDecomposition R (A j∪X i.val)
  have hP (i : M) : Fintype.card M ≤ (Finset.univ.filter (P i)).card := by
    have he : Finset.univ.filter (P i)=S.filter (fun j => HasResourceDecomposition R (A j∪X i.val)) := by
      ext j;simp [P]
    rw [he,Fintype.card_coe]
    exact_mod_cast hM.trans (hchoices i.val)
  obtain ⟨f,hf,hfP⟩ := injective_assignment_of_many_choices P (by intro i;convert hP i using 1 <;> congr!)
  let f' : M → S := fun i => ⟨f i,(hfP i).1⟩
  have hf' : Function.Injective f' := by
    intro i j hij
    exact hf (congrArg Subtype.val hij)
  have hh := assigned_absorber_reservoir R (fun i : M => X i.val) (fun j : S => A j.val)
    (fun i j hij => hXX i.val i.property j.val j.property (fun h => hij (Subtype.ext h)))
    (fun i j hij => hAA i.val i.property j.val j.property (fun h => hij (Subtype.ext h)))
    (fun i j => hXA.mono (resource_subset_union X M i.val i.property)
      (resource_subset_union A S j.val j.property))
    (fun j => hA j.val j.property) f' hf' (fun i => (hfP i).2)
  rw [biUnion_finset_subtype,biUnion_finset_subtype] at hh
  exact hh

end Oberwolfach
