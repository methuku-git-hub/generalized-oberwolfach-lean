module

public import Oberwolfach.OrdinaryDeepCountsFromCleanup
public import Oberwolfach.EndpointNeighborhoodsFromDeepCounts
public import Oberwolfach.EndpointPhysicalEditedConditions

@[expose] public section
/-! The original deeper sample and cleanup edits provide the endpoint
factor's common-neighborhood bounds on the same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem endpoint_neighborhoods_from_cleanup
    (P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
    (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
    (γ κ p pR pH density tR tH L Ledit βe βh δ ε:ℝ) (σ:RawWheelOutcome V U Γ Color)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ)
    (deep:RawOrdinaryRows P π d 3 A pR s j tR σ)
    (geom:EndpointPhysicalEditedConditions P Q F H A B Aᶜ π d j κ p pR pH L Ledit δ σ)
    (hrowbudget:tR+4*Ledit≤ε*A.card) (hindexbudget:tH+3*Ledit≤ε*B.card)
    (hLA:L≤(A.card:ℝ)/24) (hε:ε≤min (p^4/16) (p^3/2))
    (hscale:γ*Fintype.card (V⊕U)≤endpointCountCoefficient p κ*A.card)
    (hdeg:∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ)):
    ∀i:{v:V // v∉A},EndpointNeighbourCounts
      (ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B))
      (ordinaryPhysicalGraph F (fun _ _=>False))
      ((ordinaryBoundaryRimSet Q A i).image Sum.inl) ((ordinaryBoundaryRowSet H A B i).image Sum.inr)
      (γ*Fintype.card (V⊕U)):=by
  have typed:=ordinary_deep_counts_from_cleanup P Q F H A B π d j s pR pH density tR tH Ledit βe βh ε σ
    profile deep geom.edit_nonneg hrowbudget hindexbudget
  have physical:=endpoint_deep_counts_physical P Q F H A B pR pH ε typed
  exact endpoint_neighborhoods_from_deep_counts P Q F H A B γ κ p pR pH ε L geom.p_pos
    (geom.rim_lower.trans geom.rim_upper) geom.rim_lower geom.spoke_lower geom.kappa_pos geom.index_lower
    geom.conflict_nonneg hLA hε hscale hdeg geom.conflict_degree geom.rim_sub physical
end Oberwolfach
