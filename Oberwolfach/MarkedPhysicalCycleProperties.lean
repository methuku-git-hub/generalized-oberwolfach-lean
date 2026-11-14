module

public import Oberwolfach.MarkedPhysicalEdges

@[expose] public section

/-! Physical rim edges of a separated canonical marked cycle are genuine
two-element edges. Global physical injectivity also gives the common-path
cross-collision restriction without imposing any relation between roots. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)

theorem markedCycle_physical_edge_card (hm : 1≤m) (hb : 1≤b)
    (C : MarkedCycleTuple tail head ktail khead m π b) (i : Fin (m+1)) :
    (markedPhysicalEdge tail head ktail khead π
      (markedCycleTypedEdge tail head ktail khead m π b C i)).card=2 := by
  classical
  have hC := permutationSeparated_injective π b C.val C.property.1
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp only [markedCycleTypedEdge,Fin.snoc_last,markedPhysicalEdge,Sum.elim_inr]
    have he := Classical.choose_spec C.property.2.2
    rw [he.1,he.2]
    have hne : C.val (Fin.last m)≠π (C.val 0) := by
      apply Ne.symm
      apply permutationSeparated_successor_avoid π b hb C.val C.property.1
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_zero,Fin.val_last] at hh
      omega
    simp [hne]
  · simp only [markedCycleTypedEdge,Fin.snoc_castSucc,markedPhysicalEdge,Sum.elim_inl]
    have he := Classical.choose_spec (C.property.2.1 j)
    rw [he.1,he.2]
    have hne : C.val j.castSucc≠C.val j.succ := by
      intro h
      have hh := congrArg Fin.val (hC h)
      simp only [Fin.val_castSucc,Fin.val_succ] at hh
      omega
    simp [hne]

def markedCyclePhysicalEdges (C : MarkedCycleTuple tail head ktail khead m π b) : Finset (Finset V) :=
  Finset.univ.image (markedPhysicalEdge tail head ktail khead π ∘
    markedCycleTypedEdge tail head ktail khead m π b C)

theorem markedCyclePhysicalEdges_card
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedCycleTuple tail head ktail khead m π b) :
    (markedCyclePhysicalEdges tail head ktail khead m π b C).card=m+1 := by
  classical
  rw [markedCyclePhysicalEdges,Finset.card_image_of_injective _
    (markedCycle_distinct_physical_edges tail head ktail khead m π b hp C)]
  simp

theorem markedPhysicalEdge_cross_collision
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π)) (e f : E⊕K)
    (hef : markedPhysicalEdge tail head ktail khead π e=markedPhysicalEdge tail head ktail khead π f) :
    Sum.elim tail ktail e=Sum.elim tail ktail f ∧ e.isRight=f.isRight := by
  have he := hp hef
  subst f
  exact ⟨rfl,rfl⟩

end Oberwolfach
