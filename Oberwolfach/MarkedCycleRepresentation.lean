module

public import Oberwolfach.MarkedCycleIncidence
public import Oberwolfach.CopiedMarkedCapacities

@[expose] public section

/-! The sequence representation is a simple directed cycle with one marked
edge. Its typed edge occurrences and their physical images are injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem markedCycleIncidence_zero_one {V E K : Type*} [DecidableEq V]
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (C : Fin (m+1) → V)
    (hC : Function.Injective C) (e : E⊕K) :
    markedCycleIncidence tail head ktail khead m C e=0 ∨
      markedCycleIncidence tail head ktail khead m C e=1 := by
  classical
  cases e with
  | inl e =>
    simp only [markedCycleIncidence,Sum.elim_inl]
    by_cases h : ∃ j : Fin m,tail e=C j.castSucc ∧ head e=C j.succ
    · obtain ⟨j,hj⟩ := h
      right
      rw [Finset.sum_eq_single j]
      · simp only [directedEdgeIndicator,hj.1,hj.2,and_self,ite_true]
      · intro l _ hlj
        have hh : ¬(tail e=C l.castSucc ∧ head e=C l.succ) := by
          intro hl
          have he := hC (hl.1.symm.trans hj.1)
          exact hlj (Fin.castSucc_injective m he)
        simp only [directedEdgeIndicator,hh,ite_false]
      · simp
    · left
      apply Finset.sum_eq_zero
      intro j _
      simp only [directedEdgeIndicator,show ¬(tail e=C j.castSucc ∧ head e=C j.succ) from fun hj => h ⟨j,hj⟩,ite_false]
  | inr e =>
    simp only [markedCycleIncidence,Sum.elim_inr,directedEdgeIndicator]
    split_ifs <;> simp

def markedCycleTypedEdge {V E K : Type*} (tail head : E → V) (ktail khead : K → V)
    (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (C : MarkedCycleTuple tail head ktail khead m π b) : Fin (m+1) → E⊕K :=
  Fin.snoc (fun j => Sum.inl (Classical.choose (C.property.2.1 j)))
    (Sum.inr (Classical.choose C.property.2.2))

theorem markedCycleTypedEdge_endpoints {V E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (C : MarkedCycleTuple tail head ktail khead m π b) (i : Fin (m+1)) :
    Sum.elim tail ktail (markedCycleTypedEdge tail head ktail khead m π b C i)=C.val i ∧
    Sum.elim head khead (markedCycleTypedEdge tail head ktail khead m π b C i)=C.val (finRotate (m+1) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [markedCycleTypedEdge,Fin.snoc_last,Sum.elim_inr,finRotate_last]
    exact Classical.choose_spec C.property.2.2
  · simp only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.elim_inl,finRotate_castSucc_eq_succ]
    exact Classical.choose_spec (C.property.2.1 j)

theorem markedCycleTypedEdge_injective {V E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (C : MarkedCycleTuple tail head ktail khead m π b) :
    Function.Injective (markedCycleTypedEdge tail head ktail khead m π b C) := by
  intro i j hij
  apply permutationSeparated_injective π b C.val C.property.1
  rw [← (markedCycleTypedEdge_endpoints tail head ktail khead m π b C i).1,
      ← (markedCycleTypedEdge_endpoints tail head ktail khead m π b C j).1,hij]

theorem markedCycle_physical_images_injective {V E K P : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (C : MarkedCycleTuple tail head ktail khead m π b) (physical : E⊕K → P)
    (hphysical : Function.Injective physical) :
    Function.Injective (physical ∘ markedCycleTypedEdge tail head ktail khead m π b C) :=
  hphysical.comp (markedCycleTypedEdge_injective tail head ktail khead m π b C)

theorem markedCycleTypedEdge_marked_iff {V E K : Type*}
    (tail head : E → V) (ktail khead : K → V) (m : ℕ) (π : Equiv.Perm V) (b : ℕ)
    (C : MarkedCycleTuple tail head ktail khead m π b) (i : Fin (m+1)) :
    (∃ e : K,markedCycleTypedEdge tail head ktail khead m π b C i=Sum.inr e) ↔ i=Fin.last m := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [markedCycleTypedEdge,Fin.snoc_last,Sum.inr.injEq,exists_eq',iff_self]
  · simp only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.inl_ne_inr,exists_false,Fin.castSucc_ne_last,iff_self]

end Oberwolfach
