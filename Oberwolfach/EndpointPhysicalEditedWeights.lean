module

public import Oberwolfach.EndpointPhysicalInputsFromSample
public import Oberwolfach.EndpointPhysicalParentWeights
public import Oberwolfach.EndpointWeightsAfterSymmetricEdits

@[expose] public section
/-! Apply the fixed parent matching weights to every edited physical endpoint
factor on the same sampled outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem endpoint_physical_edited_weights_on_sample
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U) (X:Finset V)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (weight:V→Sym2 (V⊕U)→ℝ)
    (κ p pR pH L Ledit δ t:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (parent:EndpointPhysicalParentWeights P A X weight)
    (event:EndpointPhysicalPotentialEvent P F A B X π d j weight pR pH t σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A B X π d j κ p pR pH L Ledit δ σ):
    ∀x∈X,EndpointParentWeightSampleConclusion
      (ordinaryPhysicalGraph Q (fun _ _=>False)) (ordinaryPhysicalGraph ⊥ H)
      (ordinaryPhysicalGraph F (fun _ _=>False)) (A.image Sum.inl) (B.image Sum.inr)
      (Sum.inl x) (weight x) κ p pR pH L Ledit δ t:=by
  intro x hx
  have inp:=endpoint_physical_inputs_from_sample P Q F H A B X π d j weight κ p pR pH L Ledit δ t σ event geom x hx
  have hA:(A.image (Sum.inl:V→V⊕U)).card=A.card:=Finset.card_image_of_injective _ Sum.inl_injective
  have ha:0<((A.image (Sum.inl:V→V⊕U)).card:ℝ):=by rw [hA];exact_mod_cast geom.row_pos
  have hw:∀v∈(A.image (Sum.inl:V→V⊕U))∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x),
      ∀w∈(A.image (Sum.inl:V→V⊕U))∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x),
        0≤weight x s(v,w)∧weight x s(v,w)≤40/(A.image (Sum.inl:V→V⊕U)).card:=by
    simpa only [hA] using parent.bounded x hx
  have hp:∀e∈(endpointEligibleGraph (ordinaryPhysicalGraph P (fun _ _=>False))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((A.image (Sum.inl:V→V⊕U))∩(ordinaryPhysicalGraph P (fun _ _=>False)).neighborFinset (Sum.inl x))
      (Sum.inl x)).edgeSet,
      (1/30:ℝ)/(A.image (Sum.inl:V→V⊕U)).card≤weight x e ∧
      weight x e≤40/(A.image (Sum.inl:V→V⊕U)).card:=by
    simpa only [hA] using parent.positive x hx (ordinaryPhysicalGraph F (fun _ _=>False))
  exact endpoint_fixed_weights_after_symmetric_edits
    (ordinaryPhysicalGraph P (fun _ _=>False))
    (ordinaryPhysicalGraph (rawWheelGraph P σ) (fun _ _=>False))
    (ordinaryPhysicalGraph Q (fun _ _=>False))
    (ordinaryPhysicalGraph ⊥ (rawWheelSpokes π d σ j)) (ordinaryPhysicalGraph ⊥ H)
    (ordinaryPhysicalGraph F (fun _ _=>False)) (A.image Sum.inl) (B.image Sum.inr) (Sum.inl x)
    inp.disjoint inp.rim_sub inp.conflict_free_index κ p pR pH (1/30) 40 L Ledit δ t
    ha inp.kappa_pos inp.p_pos (by norm_num) (by norm_num) inp.conflict_nonneg inp.edit_nonneg
    inp.balance_nonneg inp.index_lower inp.index_upper inp.rim_lower inp.rim_upper inp.spoke_lower
    inp.spoke_upper inp.conflict_degree (weight x) hw (parent.mass x hx)
    (fun v _ w _=>parent.zero x hx v w) hp inp.parent_balance inp.row_potential inp.index_potential
    inp.rim_edit inp.spoke_edit
end Oberwolfach
