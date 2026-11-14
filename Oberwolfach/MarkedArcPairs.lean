module

public import Oberwolfach.MarkedWheelResources
public import Oberwolfach.OrdinaryRimPairCodegrees

@[expose] public section

/-! Distinct co-occurring arcs of a simple marked cycle force at least
three distinct auxiliary vertices, even across the two arc types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finRotate_twice_ne_self {c : ℕ} (hc : 3≤c) (i : Fin c) :
    finRotate c (finRotate c i)≠i := by
  letI : NeZero c := ⟨by omega⟩
  intro he
  simp only [finRotate_apply] at he
  have hh : (1 : Fin c)+1=0 := add_left_cancel (show i+(1+1)=i+0 by simpa only [add_assoc,add_zero] using he)
  have hv := congrArg Fin.val hh
  norm_num [Fin.val_add,Fin.val_one,Fin.val_zero,Nat.mod_eq_of_lt (show 1<c by omega),Nat.mod_eq_of_lt (show 2<c by omega)] at hv

theorem markedCycleTypedEdge_mem_iff {V E K : Type*} [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K) :
    markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b C ↔
      ∃ i,markedCycleTypedEdge tail head ktail khead m π b C i=e := by
  simp only [markedCyclePhysicalEdges,Finset.mem_image,Finset.mem_univ,true_and,
    Function.comp_apply,hp.eq_iff]

theorem marked_cycle_auxiliary_arc_nonloop {V E K : Type*} [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (hm : 1≤m) (C : MarkedCycleTuple tail head ktail khead m π b)
    (i : Fin (m+1)) : C.val i≠C.val (finRotate (m+1) i) := by
  intro he
  have hi := permutationSeparated_injective π b C.val C.property.1 he
  letI : NeZero (m+1) := ⟨by omega⟩
  rw [finRotate_apply] at hi
  have hh : (1 : Fin (m+1))=0 := add_left_cancel (show i+1=i+0 by simpa using hi.symm)
  have hv := congrArg Fin.val hh
  norm_num [Fin.val_natCast,Nat.mod_eq_of_lt (show 1<m+1 by omega)] at hv

theorem marked_cycle_arc_endpoints_present {V E K : Type*} [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K)
    (he : markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b C) :
    Sum.elim tail ktail e∈Set.range C.val ∧ Sum.elim head khead e∈Set.range C.val := by
  obtain ⟨i,hi⟩ := (markedCycleTypedEdge_mem_iff hp C e).mp he
  have h := markedCycleTypedEdge_endpoints tail head ktail khead m π b C i
  rw [hi] at h
  exact ⟨⟨i,h.1.symm⟩,⟨finRotate (m+1) i,h.2.symm⟩⟩

theorem marked_cycle_arc_nonloop {V E K : Type*} [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (hm : 1≤m) (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K)
    (he : markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b C) :
    Sum.elim tail ktail e≠Sum.elim head khead e := by
  obtain ⟨i,hi⟩ := (markedCycleTypedEdge_mem_iff hp C e).mp he
  have h := markedCycleTypedEdge_endpoints tail head ktail khead m π b C i
  rw [hi] at h
  rw [h.1,h.2]
  exact marked_cycle_auxiliary_arc_nonloop hm C i

theorem marked_cycle_distinct_auxiliary_arc_pairs {V E K : Type*} [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (hm : 2≤m) (C : MarkedCycleTuple tail head ktail khead m π b)
    (i j : Fin (m+1)) (hij : i≠j) :
    s(C.val i,C.val (finRotate (m+1) i))≠s(C.val j,C.val (finRotate (m+1) j)) := by
  intro he
  have hinj := permutationSeparated_injective π b C.val C.property.1
  rcases Sym2.eq_iff.mp he with he|he
  · exact hij (hinj he.1)
  · have h1 := hinj he.1
    have h2 := hinj he.2
    have hrot : finRotate (m+1) (finRotate (m+1) i)=i := by rw [h2,← h1]
    exact finRotate_twice_ne_self (by omega) i hrot

theorem marked_cycle_arc_pair_root_card {V E K : Type*} [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
    (hm : 2≤m) (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedCycleTuple tail head ktail khead m π b) (e f : E⊕K) (hef : e≠f)
    (he : markedPhysicalEdge tail head ktail khead π e∈markedCyclePhysicalEdges tail head ktail khead m π b C)
    (hf : markedPhysicalEdge tail head ktail khead π f∈markedCyclePhysicalEdges tail head ktail khead m π b C) :
    3≤({Sum.elim tail ktail e,Sum.elim head khead e,Sum.elim tail ktail f,Sum.elim head khead f}:Finset V).card := by
  obtain ⟨i,hi⟩ := (markedCycleTypedEdge_mem_iff hp C e).mp he
  obtain ⟨j,hj⟩ := (markedCycleTypedEdge_mem_iff hp C f).mp hf
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
