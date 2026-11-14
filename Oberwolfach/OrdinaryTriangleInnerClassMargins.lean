module

public import Oberwolfach.OrdinaryRelativeHubConditionsFromDeepSample
public import Oberwolfach.EndpointNeighborhoodsFromCleanupInnerScale

@[expose] public section
/-! The actual hub and endpoint boundary classes are large on the inner
scale. This transfers their margins to the ambient-scaled finish. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_inner_class_margins
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (κ pmin pR pH density tR tH L Ledit βe βh δ ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A B Aᶜ π d j κ pmin pR pH L Ledit δ σ)
    (hpmin1:pmin≤1) (hdensity:(3/4:ℝ)≤density)
    (hrow:tR+4*Ledit≤ε*A.card) (hindex:tH+3*Ledit≤ε*B.card)
    (hLA:L≤(A.card:ℝ)/24) (hε:ε≤min (pmin^4/16) (pmin^3/2))
    (hF:∀v,(F.degree v:ℝ)≤L)
    (hdeg:∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)):
    let γh:ℝ:=pmin^4/32;
    let γe:ℝ:=endpointCountCoefficient pmin κ/4;
    let κinner:ℝ:=min γh γe;
    let κambient:ℝ:=κinner*A.card/Fintype.card (V⊕U);
    0<κinner ∧ 0<κambient ∧
    (∀u:{u:U // u∉B},κambient*Fintype.card (V⊕U)≤((ordinaryBoundaryHubSet H B A u).card:ℝ)) ∧
    (∀v:{v:V // v∉A},κambient*Fintype.card (V⊕U)≤((ordinaryBoundaryRowSet H A B v).card:ℝ)):=by
  intro γh γe κinner κambient
  have hA:A.Nonempty:=Finset.card_pos.mp geom.row_pos
  have hAr:0<(A.card:ℝ):=by exact_mod_cast geom.row_pos
  have hn:0<(Fintype.card (V⊕U):ℝ):=by
    have hV:0<Fintype.card V:=Fintype.card_pos_iff.mpr ⟨hA.choose⟩
    have hh:Fintype.card V≤Fintype.card (V⊕U):=Fintype.card_le_of_injective Sum.inl Sum.inl_injective
    exact_mod_cast (show 0<Fintype.card (V⊕U) by omega)
  have hγh:0<γh:=by dsimp [γh];have hp:=geom.p_pos;positivity
  have hγe:0<γe:=by dsimp [γe];have hh:=endpointCountCoefficient_pos pmin κ geom.p_pos geom.kappa_pos;positivity
  have hk:0<κinner:=lt_min hγh hγe
  have hka:0<κambient:=by dsimp [κambient];positivity
  have heq:κambient*Fintype.card (V⊕U)=κinner*A.card:=by
    dsimp [κambient]
    exact div_mul_cancel₀ _ (ne_of_gt hn)
  have hγhcap:γh≤pmin^4/16:=by dsimp [γh];nlinarith [sq_nonneg (pmin^2)]
  have hc:=ordinary_relative_hub_conditions_from_deep_sample P Q F H A B π d j s γh pmin pR pH density
    tR tH L Ledit βe βh ε σ profile deep hA geom.p_pos hpmin1 geom.rim_lower geom.spoke_lower hdensity
    geom.conflict_nonneg geom.edit_nonneg hLA hF hrow (hε.trans (min_le_left _ _)) hγhcap
  have hγecap:2*γe≤endpointCountCoefficient pmin κ:=by
    dsimp [γe]
    have hh:=endpointCountCoefficient_pos pmin κ geom.p_pos geom.kappa_pos
    linarith
  have he:=endpoint_neighborhoods_from_cleanup_inner_scale P Q F H A B π d j s γe κ pmin pR pH density
    tR tH L Ledit βe βh δ ε σ profile deep geom hrow hindex hLA hε hA geom.index_upper hγe.le hγecap hdeg
  refine ⟨hk,hka,?_,?_⟩
  · intro u
    rw [heq]
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)).trans (hc.1 u)
  · intro v
    rw [heq]
    have hinner:A.card≤(ordinaryPhysicalInnerDomain A B).card:=by
      rw [ordinary_physical_inner_domain_card];omega
    have hscale:κinner*A.card≤γe*(ordinaryPhysicalInnerDomain A B).card:=by
      calc
        κinner*A.card≤γe*A.card:=mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
        _≤γe*(ordinaryPhysicalInnerDomain A B).card:=mul_le_mul_of_nonneg_left (by exact_mod_cast hinner) hγe.le
    have hv:γe*(ordinaryPhysicalInnerDomain A B).card≤
        (((ordinaryBoundaryRowSet H A B v).image (Sum.inr:U→V⊕U)).card:ℝ):=(he v).indices
    simpa only [Finset.card_image_of_injective _ Sum.inr_injective] using hscale.trans hv
end Oberwolfach
