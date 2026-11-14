module

public import Oberwolfach.FactorWalkOrderedEdges

@[expose] public section
/-! Removing a simple path deletes one more edge than internal vertices. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

theorem simple_path_edges_and_internal_vertices (F:SimpleGraph V) {u v:V}
    (p:F.Walk u v) (hp:p.IsPath) (huv:u≠v):
    p.edges.toFinset.card = (p.support.toFinset \ {u,v}).card + 1 := by
  have hs : p.support.toFinset.card=p.length+1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  have he : p.edges.toFinset.card=p.length := by
    rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup, p.length_edges]
  have hsub : ({u,v}:Finset V)⊆p.support.toFinset := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl
    · simpa using p.start_mem_support
    · simpa using p.end_mem_support
  have hpair : ({u,v}:Finset V).card=2 := by simp [huv]
  have hdiff := Finset.card_sdiff_add_card_eq_card hsub
  rw [hpair,hs] at hdiff
  omega
end Oberwolfach
