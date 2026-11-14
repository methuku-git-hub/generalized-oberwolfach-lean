module

public import Oberwolfach.MarkedInitialDiagramOldResources

@[expose] public section

/-! Locate the actual root resources through their typed occurrences.
Disjoint auxiliary root sets imply disjoint physical root graphs under
exactly the original physical injectivity hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype A] [Fintype S] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

theorem marked_root_rim_occurrence (src dst:A→V) (jr:A→Bool)
    (hroot:∀ a,if jr a then ∃ k,ktail k=src a∧khead k=dst a else ∃ e,tail e=src a∧head e=dst a)
    (a:A):∃ k:E⊕K,
      markedPhysicalEdge tail head ktail khead π k=(if jr a then ({src a,π (dst a)}:Finset V) else {src a,dst a})∧
      Sum.elim tail ktail k=src a∧Sum.elim head khead k=dst a:=by
  have h:=hroot a
  cases hj:jr a with
  | false=>
    simp only [hj,Bool.false_eq_true,ite_false] at h ⊢
    obtain ⟨e,he⟩:=h
    exact ⟨Sum.inl e,by simp only [markedPhysicalEdge,Sum.elim_inl,he.1,he.2],he.1,he.2⟩
  | true=>
    simp only [hj,ite_true] at h ⊢
    obtain ⟨e,he⟩:=h
    exact ⟨Sum.inr e,by simp only [markedPhysicalEdge,Sum.elim_inr,he.1,he.2],he.1,he.2⟩

theorem marked_root_graph_old_supported (src dst:A→V) (row:S→V) (jr:A→Bool) (u:S→U)
    (Z:Finset V) (B:Finset U) (hR:∀ a,src a∈Z∧dst a∈Z) (hS:∀ s,row s∈Z∧u s∈B)
    (hroot:∀ a,if jr a then ∃ k,ktail k=src a∧khead k=dst a else ∃ e,tail e=src a∧head e=dst a):
    ∀ e∈markedRootGraphResources π src dst row jr u,
      MarkedOldResource tail head ktail khead π Z B e∧MarkedResourceSupported tail head ktail khead π Z e:=by
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨k,hk,ht,hh⟩:=marked_root_rim_occurrence (π:=π) src dst jr hroot a
    have hsp:∃ k:E⊕K,markedPhysicalEdge tail head ktail khead π k=(if jr a then {src a,π (dst a)} else {src a,dst a})∧
        Sum.elim tail ktail k∈Z∧Sum.elim head khead k∈Z:=
      ⟨k,hk,ht.symm ▸ (hR a).1,hh.symm ▸ (hR a).2⟩
    exact ⟨hsp,hsp⟩
  · obtain ⟨s,_,rfl⟩:=Finset.mem_image.mp he
    exact ⟨hS s,(hS s).1⟩

end Oberwolfach
