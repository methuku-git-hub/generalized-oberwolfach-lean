module

public import Oberwolfach.EndpointPhysicalEditedConditions
public import Oberwolfach.EndpointParentWeightSampleInputs
public import Oberwolfach.EndpointTypedParentGeometry

@[expose] public section
/-! Turn the same-sample physical potential event and later edit conditions
into the exact fixed-weight endpoint input at each boundary root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem endpoint_physical_inputs_from_sample
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (X:Finset V)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ)
    (κ p pR pH L Ledit δ t:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (event:EndpointPhysicalPotentialEvent P F A B X π d j weight pR pH t σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A B X π d j κ p pR pH L Ledit δ σ):
    ∀x∈X,EndpointParentWeightSampleInputs
      (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph (rawWheelGraph P σ) (fun _ _=>False))
      (ordinaryPhysicalGraph Q (fun _ _=>False))
      (ordinaryPhysicalGraph ⊥ (rawWheelSpokes π d σ j)) (ordinaryPhysicalGraph ⊥ H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (A.image Sum.inl) (B.image Sum.inr)
      (Sum.inl x) (weight x) κ p pR pH L Ledit δ t:=by
  intro x hx
  have hA:(A.image (Sum.inl:V→V⊕U)).card=A.card:=Finset.card_image_of_injective _ Sum.inl_injective
  have hB:(B.image (Sum.inr:U→V⊕U)).card=B.card:=Finset.card_image_of_injective _ Sum.inr_injective
  refine
    { disjoint := ?_
      rim_sub := geom.rim_sub
      conflict_free_index := ?_
      kappa_pos := geom.kappa_pos
      p_pos := geom.p_pos
      conflict_nonneg := geom.conflict_nonneg
      edit_nonneg := geom.edit_nonneg
      balance_nonneg := geom.balance_nonneg
      index_lower := ?_
      index_upper := ?_
      rim_lower := geom.rim_lower
      rim_upper := geom.rim_upper
      spoke_lower := geom.spoke_lower
      spoke_upper := geom.spoke_upper
      conflict_degree := geom.conflict_degree
      parent_balance := ?_
      row_potential := ?_
      index_potential := ?_
      rim_edit := geom.rim_edit
      spoke_edit := geom.spoke_edit }
  · apply Finset.disjoint_left.mpr
    intro z hzA hzB
    cases z with
    | inl v=>simp at hzB
    | inr u=>simp at hzA
  · intro u hu w
    obtain ⟨u₀,hu₀,rfl⟩:=Finset.mem_image.mp hu
    cases w <;> simp [ordinaryPhysicalGraph]
  · simpa only [hA,hB] using geom.index_lower
  · simpa only [hA,hB] using geom.index_upper
  · have hh:=geom.parent_balance x hx
    simpa only [ordinary_endpoint_parent_neighbors,Finset.card_image_of_injective _ Sum.inl_injective,hB] using hh
  · intro v hv
    have hh:=event.row x hx v hv
    simpa only [hB] using hh.le
  · intro u hu
    obtain ⟨u₀,hu₀,rfl⟩:=Finset.mem_image.mp hu
    have hh:=event.index x hx u₀ hu₀
    simpa only [hB] using hh.le
end Oberwolfach
