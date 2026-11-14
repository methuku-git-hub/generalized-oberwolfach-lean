module

public import Oberwolfach.MixedWheelRimPacksDisjoint

@[expose] public section

/-! Each vertex of a marked tuple is incident with a physical rim edge. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_marked_tuple_vertex_in_rim
    {V E K:Type} [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (m:ℕ) (π:Equiv.Perm V) (b:ℕ)
    (C:MarkedCycleTuple tail head ktail khead m π b) (i:Fin (m+1)):
    ∃edge∈markedCyclePhysicalEdges tail head ktail khead m π b C,C.val i∈edge :=by
  let edge:=markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C i)
  refine ⟨edge,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · dsimp [edge]
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simp only [markedCycleTypedEdge,Fin.snoc_last,markedPhysicalEdge,Sum.elim_inr]
      have h:=Classical.choose_spec C.property.2.2
      rw [h.1]
      simp
    · simp only [markedCycleTypedEdge,Fin.snoc_castSucc,markedPhysicalEdge,Sum.elim_inl]
      have h:=Classical.choose_spec (C.property.2.1 j)
      rw [h.1]
      simp
end Oberwolfach
