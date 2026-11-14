module

public import Oberwolfach.PrescribedEdgeEnumeration
public import Oberwolfach.OrdinaryPackingTransport

@[expose] public section

/-! Separate rim, spoke-row and spoke-column bounds imply the combined
physical incidence bound used to enumerate a prescribed edge set.
The row bound is twice the separate bound; no orientation multiplicity is added. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinaryHostResources_filter_incident (Q:SimpleGraph V) (H:V→U→Prop) (x:V⊕U):
    (ordinaryHostResources Q H).filter (ordinaryResourceIncident x)=ordinaryPhysicalIncidentEdges Q H x:=by
  ext e
  simp only [ordinaryHostResources,ordinaryPhysicalIncidentEdges,Finset.mem_filter,
    Finset.mem_univ,true_and]

theorem prescribed_physical_incidence_bound (Q:SimpleGraph V) (H:V→U→Prop)
    (E:Finset (Sym2 V⊕(V×U))) (D:ℕ) (hE:E⊆ordinaryHostResources Q H)
    (hr:∀ v,Q.degree v≤D)
    (hs:∀ v,(Finset.univ.filter (H v)).card≤D)
    (hc:∀ u,(Finset.univ.filter (fun v=>H v u)).card≤D):
    ∀ x,(E.filter (ordinaryResourceIncident x)).card≤2*D:=by
  intro x
  have hh:(E.filter (ordinaryResourceIncident x)).card≤(ordinaryPhysicalIncidentEdges Q H x).card:=by
    rw [←ordinaryHostResources_filter_incident]
    exact Finset.card_le_card (Finset.filter_subset_filter _ hE)
  apply hh.trans
  cases x with
  | inl v=>rw [ordinaryPhysicalIncidentEdges_rim_card];exact (Nat.add_le_add (hr v) (hs v)).trans_eq (two_mul D).symm
  | inr u=>rw [ordinaryPhysicalIncidentEdges_hub_card];exact (hc u).trans (by omega)

end Oberwolfach
