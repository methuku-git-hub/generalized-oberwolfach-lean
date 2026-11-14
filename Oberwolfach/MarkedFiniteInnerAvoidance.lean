module

public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section

/-! An empty physical induced intersection is equivalent to explicit
endpoint and spoke exclusions when the row set is permutation-invariant. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_finite_inner_empty_iff
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (I:Finset V) (J:Finset U)
    (hI:∀ v,π v∈I↔v∈I):
    (markedFiniteResources tail head ktail khead π A S).filter (markedInnerResource I J)=∅↔
      (∀ a∈A,¬(Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))∧
      (∀ z∈S,¬(z.1∈I∧z.2∈J)):=by
  constructor
  · intro h
    constructor
    · intro a ha hi
      have hm:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈
          (markedFiniteResources tail head ktail khead π A S).filter (markedInnerResource I J):=by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩),?_⟩
        exact (marked_physical_edge_inner_iff I hI a).mpr hi
      rw [h] at hm
      exact Finset.notMem_empty _ hm
    · intro z hz hi
      have hm:Sum.inr z∈(markedFiniteResources tail head ktail khead π A S).filter (markedInnerResource I J):=
        Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩),hi⟩
      rw [h] at hm
      exact Finset.notMem_empty _ hm
  · rintro ⟨ha,hs⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨hz,hi⟩:=Finset.mem_filter.mp hz
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨a,ha',rfl⟩:=Finset.mem_image.mp hz
      exact ha a ha' ((marked_physical_edge_inner_iff I hI a).mp hi)
    · obtain ⟨pair,hpair,heq⟩:=Finset.mem_image.mp hz
      subst z
      exact hs pair hpair hi

end Oberwolfach
