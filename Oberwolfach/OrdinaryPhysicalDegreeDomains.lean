module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! Rim and spoke degrees are the two disjoint domain degrees of the
physical graph on rim vertices and hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryPhysicalRimDomain : Finset (V⊕U):=Finset.univ.image Sum.inl
def ordinaryPhysicalHubDomain : Finset (V⊕U):=Finset.univ.image Sum.inr

theorem ordinary_physical_left_degree (G:SimpleGraph (V⊕U)) (v:V):
    (ordinaryPhysicalRimDomain ∩ G.neighborFinset (Sum.inl v)).card=
      (G.comap Sum.inl).degree v:=by
  have he:ordinaryPhysicalRimDomain ∩ G.neighborFinset (Sum.inl v)=
      ((G.comap Sum.inl).neighborFinset v).image Sum.inl:=by
    ext z
    cases z with
    | inl w=>simp [ordinaryPhysicalRimDomain,SimpleGraph.mem_neighborFinset,SimpleGraph.comap]
    | inr u=>simp [ordinaryPhysicalRimDomain]
  rw [he,Finset.card_image_of_injective _ Sum.inl_injective,SimpleGraph.card_neighborFinset_eq_degree]

theorem ordinary_physical_right_degree (G:SimpleGraph (V⊕U)) (v:V):
    (ordinaryPhysicalHubDomain ∩ G.neighborFinset (Sum.inl v)).card=
      (Finset.univ.filter (fun u=>G.Adj (Sum.inl v) (Sum.inr u))).card:=by
  have he:ordinaryPhysicalHubDomain ∩ G.neighborFinset (Sum.inl v)=
      (Finset.univ.filter (fun u=>G.Adj (Sum.inl v) (Sum.inr u))).image Sum.inr:=by
    ext z
    cases z with
    | inl w=>simp [ordinaryPhysicalHubDomain]
    | inr u=>simp [ordinaryPhysicalHubDomain,SimpleGraph.mem_neighborFinset]
  rw [he,Finset.card_image_of_injective _ Sum.inr_injective]
end Oberwolfach
