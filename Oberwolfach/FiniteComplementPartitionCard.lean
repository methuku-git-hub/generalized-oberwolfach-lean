module

public import Oberwolfach.MarkedPackingVertexCount

@[expose] public section
/-! The cardinality identity for two disjoint sets and their complement. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_complement_partition_card
    {V:Type*} [Fintype V] [DecidableEq V] (S B:Finset V) (hdis:Disjoint S B):
    S.card=Fintype.card V-(Finset.univ\(S∪B)).card-B.card := by
  have h:=Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (S∪B))
  rw [Finset.card_union_of_disjoint hdis,Finset.card_univ] at h
  omega
end Oberwolfach
