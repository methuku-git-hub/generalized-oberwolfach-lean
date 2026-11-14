module

public import Oberwolfach.MarkedArcPairs

@[expose] public section

/-! Membership of an actual typed arc in a canonical cycle. No global
injectivity of physical images is imposed on the potential arc universe. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

variable {V E K : Type*} [DecidableEq V]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}

def CanonicalMarkedArcMem (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K) : Prop :=
  ∃ i,markedCycleTypedEdge tail head ktail khead m π b C i=e

theorem canonicalMarkedArc_endpoints_present
    (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K)
    (he : CanonicalMarkedArcMem C e) :
    Sum.elim tail ktail e∈Set.range C.val ∧ Sum.elim head khead e∈Set.range C.val := by
  obtain ⟨i,hi⟩ := he
  have h := markedCycleTypedEdge_endpoints tail head ktail khead m π b C i
  rw [hi] at h
  exact ⟨⟨i,h.1.symm⟩,⟨finRotate (m+1) i,h.2.symm⟩⟩

theorem canonicalMarkedArc_nonloop (hm : 1≤m)
    (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K)
    (he : CanonicalMarkedArcMem C e) :
    Sum.elim tail ktail e≠Sum.elim head khead e := by
  obtain ⟨i,hi⟩ := he
  have h := markedCycleTypedEdge_endpoints tail head ktail khead m π b C i
  rw [hi] at h
  rw [h.1,h.2]
  exact marked_cycle_auxiliary_arc_nonloop hm C i

theorem canonicalMarkedArc_pair_root_card (hm : 2≤m)
    (C : MarkedCycleTuple tail head ktail khead m π b) (e f : E⊕K) (hef : e≠f)
    (he : CanonicalMarkedArcMem C e) (hf : CanonicalMarkedArcMem C f) :
    3≤({Sum.elim tail ktail e,Sum.elim head khead e,Sum.elim tail ktail f,Sum.elim head khead f}:Finset V).card := by
  obtain ⟨i,hi⟩ := he
  obtain ⟨j,hj⟩ := hf
  have hij : i≠j := by intro h;subst j;exact hef (hi.symm.trans hj)
  have hei := markedCycleTypedEdge_endpoints tail head ktail khead m π b C i
  have hej := markedCycleTypedEdge_endpoints tail head ktail khead m π b C j
  rw [hi] at hei
  rw [hj] at hej
  rw [hei.1,hei.2,hej.1,hej.2]
  exact (distinct_pair_union_card _ _ _ _
    (marked_cycle_auxiliary_arc_nonloop (by omega) C i)
    (marked_cycle_auxiliary_arc_nonloop (by omega) C j)
    (marked_cycle_distinct_auxiliary_arc_pairs hm C i j hij)).1

end Oberwolfach
