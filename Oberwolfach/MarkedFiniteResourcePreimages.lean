module

public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section

/-! Recover the actual typed arc and spoke sets of any finite subset of a
host's physical resources. The construction is used for the next error
set after cover-down, rather than assuming a new typed representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_finite_resource_preimages
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (F : Finset (Finset V⊕(V×U)))
    (hF : F⊆markedFiniteResources tail head ktail khead π A S) :
    let FA := A.filter (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈F)
    let FS := S.filter (fun s=>Sum.inr s∈F);
    FA⊆A ∧ FS⊆S ∧ markedFiniteResources tail head ktail khead π FA FS=F := by
  intro FA FS
  refine ⟨Finset.filter_subset _ _,Finset.filter_subset _ _,?_⟩
  ext z
  constructor
  · intro hz
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp ha).2
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp hs).2
  · intro hz
    rcases Finset.mem_union.mp (hF hz) with hh|hh
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hh
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hz⟩,rfl⟩)
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hh
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨hs,hz⟩,rfl⟩)

theorem marked_finite_resources_determine_sets
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A B : Finset (E⊕K)) (S T : Finset (V×U))
    (h : markedFiniteResources tail head ktail khead π A S=markedFiniteResources tail head ktail khead π B T) :
    A=B ∧ S=T := by
  constructor
  · ext a
    rw [←markedFiniteResources_rim tail head ktail khead π hp A S a,h,
      markedFiniteResources_rim tail head ktail khead π hp B T a]
  · ext s
    rw [←markedFiniteResources_spoke tail head ktail khead π A S s,h,
      markedFiniteResources_spoke tail head ktail khead π B T s]

end Oberwolfach
