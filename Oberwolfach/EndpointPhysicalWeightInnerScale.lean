module

public import Oberwolfach.EndpointPhysicalEditedWeights
public import Oberwolfach.EndpointWeightScaleTransfer
public import Oberwolfach.OrdinaryEndpointPhysicalGeometry

@[expose] public section
/-! Put the edited endpoint matching weights on the actual inner host and
boundary classes, normalized by the inner vertex count. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem endpoint_physical_weight_inner_scale
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ)
    (κ p pR pH L Ledit δ t η:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:EndpointPhysicalPotentialEvent P F A B Aᶜ π d j weight pR pH t σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A B Aᶜ π d j κ p pR pH L Ledit δ σ)
    (herr:δ+(2*40+(1+2*40)/(2*κ*p))*L/A.card+(t+10*(40/(κ*p^5))*Ledit/A.card)≤η):
    ∀i:{v:V // v∉A},∃wt:EndpointTriangle
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((ordinaryBoundaryRimSet Q A i).image Sum.inl) ((ordinaryBoundaryRowSet H A B i).image Sum.inr)→ℝ,
      (∀C,(1/30:ℝ)/(A.card:ℝ)^2≤wt C ∧
        wt C≤(40/(κ*p^5))/(A.card:ℝ)^2) ∧
      (∀v∈((ordinaryBoundaryRimSet Q A i).image Sum.inl)∪((ordinaryBoundaryRowSet H A B i).image Sum.inr),
        |1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η):=by
  intro i
  have hi:i.val∈Aᶜ:=by simpa using i.property
  have hh:=endpoint_physical_edited_weights_on_sample P Q F H A B Aᶜ π d j weight κ p pR pH L Ledit δ t σ parent event geom i.val hi
  dsimp only [EndpointParentWeightSampleConclusion] at hh
  rw [ordinary_endpoint_host_physical_geometry,ordinary_endpoint_row_domain Q A i,
    ordinary_endpoint_index_domain H A B i] at hh
  have hA:(A.image (Sum.inl:V→V⊕U)).card=A.card:=Finset.card_image_of_injective _ Sum.inl_injective
  have hB:(B.image (Sum.inr:U→V⊕U)).card=B.card:=Finset.card_image_of_injective _ Sum.inr_injective
  simp only [hA,hB] at hh
  let wt:=fun C:EndpointTriangle
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((ordinaryBoundaryRimSet Q A i).image Sum.inl) ((ordinaryBoundaryRowSet H A B i).image Sum.inr)=>
        weight i.val (endpointTriangleRowEdge C)/(B.card*pR^2*pH^3)
  refine ⟨wt,?_,?_⟩
  · exact hh.1
  · intro v hv
    exact (hh.2 v hv).trans herr
end Oberwolfach
