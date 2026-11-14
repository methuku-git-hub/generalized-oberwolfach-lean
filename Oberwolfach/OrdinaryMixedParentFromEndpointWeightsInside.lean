module

public import Oberwolfach.OrdinaryMixedOtherParentInputsInside
public import Oberwolfach.EndpointPhysicalWeightAmbientScale
public import Oberwolfach.PhysicalWheelFamilies

@[expose] public section
/-! The same-sample endpoint estimates discharge all endpoint weight fields
of the fresh mixed-factor input. The remaining fields are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def ordinary_mixed_parent_from_endpoint_weights_inside
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (Z:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ)
    (γ κ b B ε η κe p pR pH L Ledit δ t K:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (parent:EndpointPhysicalParentWeights P A Aᶜ weight)
    (event:EndpointPhysicalPotentialEvent P F A Z Aᶜ π d j weight pR pH t σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A Z Aᶜ π d j κe p pR pH L Ledit δ σ)
    (hK:0≤K) (hsize:(Fintype.card (V⊕U):ℝ)≤K*A.card)
    (herr:δ+(2*40+(1+2*40)/(2*κe*p))*L/A.card+(t+10*(40/(κe*p^5))*Ledit/A.card)≤η)
    (hb:b≤1/30) (hB:(40/(κe*p^5))*K^2≤B)
    (other:OrdinaryMixedOtherParentInputsInside γ κ b B ε η Q F H A Z):
    MixedFreshParentDataInsideRoots γ κ b B ε η (spanningRestriction Q A) F
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈Z))
      (ordinaryPhysicalGraph F (fun _ _=>False)) (Function.Embedding.inl:V↪V⊕U)
      (ordinaryBoundaryHubSet H Z A) (fun i=>(ordinaryBoundaryRimSet Q A i).image Sum.inl)
      (fun i=>(ordinaryBoundaryRowSet H A Z i).image Sum.inr):=by
  have hex:=endpoint_physical_weight_ambient_scale P Q F H A Z π d j weight κe p pR pH L Ledit δ t K η σ
    parent event geom hK hsize herr
  choose ew hew hload using hex
  refine
    { mapped_host := ?_
      endpoint_disjoint := ordinary_boundary_root_domains_disjoint Q H A Z
      hub_size := other.hub_size
      rim_conflict := other.rim_conflict
      physical_conflict := other.physical_conflict
      hub_neighborhoods := other.hub_neighborhoods
      endpoint_neighborhoods := other.endpoint_neighborhoods
      hub_weight := other.hub_weight
      endpoint_weight := ew
      hub_weight_bounds := other.hub_weight_bounds
      endpoint_weight_bounds := ?_
      hub_weight_load := other.hub_weight_load
      endpoint_weight_load := hload }
  · rw [graph_map_inl_physical]
    intro x y hxy
    cases x <;> cases y <;> simpa [ordinaryPhysicalGraph] using hxy
  · intro i C
    refine ⟨?_,?_⟩
    · exact (div_le_div_of_nonneg_right hb (by positivity)).trans (hew i C).1
    · exact (hew i C).2.trans (div_le_div_of_nonneg_right hB (by positivity))
end Oberwolfach
