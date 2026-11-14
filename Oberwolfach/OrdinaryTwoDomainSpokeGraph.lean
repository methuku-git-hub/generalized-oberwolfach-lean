module

public import Oberwolfach.OrdinaryPhysicalSpokeChanges
public import Oberwolfach.BipartiteRelationGraph

@[expose] public section
/-! The undirected auxiliary bipartite graph is exactly the physical graph
of its restricted rim-to-hub relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinarySumRimSet:Finset (V⊕U):=Finset.univ.image Sum.inl

def ordinarySumHubSet (B:Finset U):Finset (V⊕U):=B.image Sum.inr

theorem ordinary_sum_domains_disjoint (B:Finset U):
    Disjoint (ordinarySumRimSet (V:=V) (U:=U)) (ordinarySumHubSet (V:=V) B):=by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp hx
  obtain ⟨u,_,he⟩:=Finset.mem_image.mp hy
  exact Sum.inr_ne_inl he

theorem ordinary_sum_bipartite_graph (B:Finset U) (E:(V⊕U)→(V⊕U)→Prop):
    bipartiteRelationGraph (ordinarySumRimSet (V:=V) (U:=U)) (ordinarySumHubSet (V:=V) B)
      (ordinary_sum_domains_disjoint B) E=
    ordinaryPhysicalSpokeGraph (fun v u=>u∈B∧E (Sum.inl v) (Sum.inr u)):=by
  ext a b
  cases a <;> cases b <;>
    simp [bipartiteRelationGraph,ordinarySumRimSet,ordinarySumHubSet,ordinaryPhysicalSpokeGraph,ordinaryPhysicalGraph]
end Oberwolfach
