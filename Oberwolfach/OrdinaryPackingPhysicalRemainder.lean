module

public import Oberwolfach.OrdinaryPackingGlue
public import Oberwolfach.PrescribedPhysicalDegrees
public import Oberwolfach.PhysicalHostDegreeBounds

@[expose] public section
/-! The uncovered incidence bound of an ordinary packing is exactly the
degree of its actual physical remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
variable {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}

theorem ordinary_unreserved_packing_resources_eq_host (M:Finset (OrdinaryWheel Q F H r)):
    M.biUnion ordinaryWheelResources=ordinaryHostResources (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M):=by
  ext e
  cases e with
  | inl e=>
    induction e using Sym2.ind with
    | _ v w=>
      rw [ordinaryHostResources_rim]
      simp only [Finset.mem_biUnion,ordinaryWheelResources_rim,SimpleGraph.mem_edgeSet]
      exact (ordinaryWheelRimGraph_edges M s(v,w)).symm
  | inr vu=>
    obtain ⟨v,u⟩:=vu
    rw [ordinaryHostResources_spoke,ordinaryPackingSpokes_iff]

theorem ordinary_physical_incident_card_eq_degree (Q:SimpleGraph V) (H:V→U→Prop) (x:V⊕U):
    (ordinaryPhysicalIncidentEdges Q H x).card=(ordinaryPhysicalGraph Q H).degree x:=by
  cases x with
  | inl v=>rw [ordinaryPhysicalIncidentEdges_rim_card,ordinary_physical_degree_row]
  | inr u=>rw [ordinaryPhysicalIncidentEdges_hub_card,ordinary_physical_degree_column]

theorem ordinary_packing_leftover_physical_degree (M:Finset (OrdinaryWheel Q F H r)) (x:V⊕U):
    (ordinaryPhysicalGraph (Q\ordinaryWheelRimGraph M) (fun v u=>H v u∧¬ordinaryPackingSpokes M v u)).degree x=
      (ordinaryIncidentEdges Q H x\M.biUnion ordinaryActiveResources).card:=by
  rw [ordinary_leftover_card_physical]
  rw [←ordinary_physical_incident_card_eq_degree,ordinaryPhysicalIncidentEdges_delete]
  rw [←ordinaryHostResources_filter_incident (ordinaryWheelRimGraph M) (ordinaryPackingSpokes M) x,
    ←ordinary_unreserved_packing_resources_eq_host M]
  congr 1
  ext e
  simp only [Finset.mem_sdiff,Finset.mem_filter,ordinaryPhysicalIncidentEdges,Finset.mem_univ,true_and]
  tauto
end Oberwolfach
