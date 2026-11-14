module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Union
public import Mathlib.Tactic

@[expose] public section

/-! Partitioning a set with prescribed class sizes into root sets with
exactly one prescribed class profile. This is a vertex partition, with
no assumptions about graph edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem profile_root_partition (A : I → Finset V) (a : I → ℕ) (q : ℕ)
    (hA : ∀ i,(A i).card=a i*q)
    (hdisj : ∀ i j,i≠j → Disjoint (A i) (A j)) :
    ∃ X : Fin q → Finset V,
      Finset.univ.biUnion X=Finset.univ.biUnion A ∧
      (∀ j k,j≠k → Disjoint (X j) (X k)) ∧
      ∀ j i,(X j∩A i).card=a i := by
  let e (i : I) : Fin q×Fin (a i) ≃ A i := Fintype.equivOfCardEq (by simp [hA i,Nat.mul_comm])
  let Y (j : Fin q) (i : I) : Finset V := Finset.univ.image (fun t : Fin (a i) => (e i (j,t)).val)
  let X (j : Fin q) : Finset V := Finset.univ.biUnion (Y j)
  have hYA (j : Fin q) (i : I) : Y j i ⊆ A i := by
    intro v hv
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hv
    exact (e i (j,t)).property
  have hYne (j k : Fin q) (hjk : j≠k) (i : I) : Disjoint (Y j i) (Y k i) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hv
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hw
    have he : e i (j,t)=e i (k,s) := Subtype.ext (ht.trans hs.symm)
    exact hjk (congrArg Prod.fst ((e i).injective he))
  have hYcard (j : Fin q) (i : I) : (Y j i).card=a i := by
    have hf : Function.Injective (fun t : Fin (a i) => (e i (j,t)).val) := by
      intro t s he
      exact congrArg Prod.snd ((e i).injective (Subtype.ext he))
    simpa only [Y,Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_fin]
  refine ⟨X,?_,?_,?_⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hj
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hYA j i hi⟩
    · intro hv
      obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
      obtain ⟨⟨j,t⟩,hjt⟩ := (e i).surjective ⟨v,hi⟩
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨t,Finset.mem_univ _,congrArg Subtype.val hjt⟩⟩⟩
  · intro j k hjk
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i',_,hi'⟩ := Finset.mem_biUnion.mp hw
    by_cases hii : i=i'
    · subst i'
      exact (Finset.disjoint_left.mp (hYne j k hjk i)) hi hi'
    · exact (Finset.disjoint_left.mp (hdisj i i' hii)) (hYA j i hi) (hYA k i' hi')
  · intro j i
    have he : X j∩A i=Y j i := by
      ext v
      constructor
      · intro hv
        obtain ⟨i',_,hi'⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hv).1
        have hii : i'=i := by
          by_contra h
          exact (Finset.disjoint_left.mp (hdisj i' i h)) (hYA j i' hi') (Finset.mem_inter.mp hv).2
        simpa only [hii] using hi'
      · intro hv
        exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩,hYA j i hv⟩
    rw [he,hYcard]

end Oberwolfach
