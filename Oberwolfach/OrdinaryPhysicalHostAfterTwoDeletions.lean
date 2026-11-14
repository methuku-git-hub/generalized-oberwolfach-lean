module

public import Oberwolfach.OrdinaryBoundaryPhysicalDeletion

@[expose] public section
/-! The actual typed host after two physical deletions retains every
candidate-host edge outside their union. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_graph_after_two_deletions (Q:SimpleGraph V) (H:V→U→Prop)
    (C D:SimpleGraph (V⊕U)):
    ordinaryPhysicalGraph ((Q\C.comap Sum.inl)\D.comap Sum.inl)
      (ordinarySpokesAfterPhysicalDeletion (ordinarySpokesAfterPhysicalDeletion H C) D)=
      ordinaryPhysicalGraph Q H\(C⊔D):=by
  rw [ordinary_physical_graph_after_deletion,ordinary_physical_graph_after_deletion]
  ext a b
  simp only [SimpleGraph.sdiff_adj,SimpleGraph.sup_adj]
  tauto

theorem ordinary_candidate_edges_survive_two_deletions (Q Q₀:SimpleGraph V) (H H₀:V→U→Prop)
    (C D:SimpleGraph (V⊕U)) (hsub:ordinaryPhysicalGraph Q H≤ordinaryPhysicalGraph Q₀ H₀):
    ordinaryPhysicalGraph Q H\(C⊔D)≤
      ordinaryPhysicalGraph ((Q₀\C.comap Sum.inl)\D.comap Sum.inl)
        (ordinarySpokesAfterPhysicalDeletion (ordinarySpokesAfterPhysicalDeletion H₀ C) D):=by
  rw [ordinary_physical_graph_after_two_deletions]
  intro a b hab
  exact ⟨hsub hab.1,hab.2⟩
end Oberwolfach
