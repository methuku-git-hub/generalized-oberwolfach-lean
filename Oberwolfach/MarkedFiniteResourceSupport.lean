module

public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section

/-! Equivalence between support of the actual typed sets and support of
their physical resources on an invariant inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem markedFiniteResources_support_iff
    (tail head : E→V) (ktail khead : K→V) (π : Equiv.Perm V)
    (A : Finset (E⊕K)) (S : Finset (V×U)) (I : Finset V) (J : Finset U)
    (hI : ∀ x,π x∈I↔x∈I) :
    (∀ z∈markedFiniteResources tail head ktail khead π A S,markedInnerResource I J z)↔
      (∀ a∈A,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I) ∧
      (∀ s∈S,s.1∈I∧s.2∈J) := by
  constructor
  · intro h
    constructor
    · intro a ha
      have hh := h (Sum.inl (markedPhysicalEdge tail head ktail khead π a))
        (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
      exact (marked_physical_edge_inner_iff I hI a).mp hh
    · intro s hs
      exact h (Sum.inr s) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨s,hs,rfl⟩))
  · rintro ⟨hA,hS⟩ z hz
    rcases Finset.mem_union.mp hz with hz|hz
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact (marked_physical_edge_inner_iff I hI a).mpr (hA a ha)
    · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hz
      exact hS s hs

end Oberwolfach
