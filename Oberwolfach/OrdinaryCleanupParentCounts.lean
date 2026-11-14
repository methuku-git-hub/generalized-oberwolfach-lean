module

public import Oberwolfach.OrdinaryCleanupParentProfiles

@[expose] public section
/-! The packaged common-sample profile yields the two cleanup extension
counts after any packing preserving the inner and reserved edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_counts_from_parent_profile
    (P Q₀ Q F:SimpleGraph V) (H₀ H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ)
    (X:Finset V) (Z:Finset U) (C:SimpleGraph (V⊕U))
    (pR pH p density tR tH L βe βh:ℝ) (s:U→Color→ℝ) (j:Color)
    (raw:RawWheelOutcome V U Γ Color) (σ:Sym2 (V⊕U)→Bool)
    (profile:OrdinaryCleanupParentProfiles P Q₀ F H₀ π d X Z pR pH density tR tH L βe βh s j raw)
    (hQ:Q≤Q₀)
    (hinner:Disjoint C (spanningRestriction (ordinaryPhysicalGraph Q₀ H₀) (ordinaryInnerVertices X Z)))
    (hreserve:Disjoint C (retainedGraph (ordinaryBoundaryGraph Q₀ H₀ X Z) σ))
    (hkeep:ordinaryPhysicalGraph Q₀ H₀\C≤ordinaryPhysicalGraph Q H)
    (hevent:OrdinaryBoundaryExtensionGood Q₀ H₀ X βe p σ)
    (hhevent:OrdinaryBoundaryHubPairGood H₀ Z βh p σ):
    (∀u a c,(p^3*βe/2)*Fintype.card (V⊕U)≤
      (((X.filter (fun v=>H v u))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ)) ∧
    (∀a∉X,∀c∉X,Q.Adj a c→(p^2*βh/2)*Fintype.card (V⊕U)≤
      ((Z.filter (fun u=>H a u∧H c u)).card:ℝ)):=by
  have hh:=ordinary_cleanup_counts_from_common_and_fresh_samples P Q₀ Q F H₀ H π d X Z C
    pR pH p density tR tH L βe βh profile.rim_nonneg profile.rim_le_one profile.spoke_nonneg
    profile.density_large s j raw σ profile.spoke_probability hQ profile.forbidden_disjoint
    profile.parent_min_degree profile.rows profile.columns profile.rim_edit profile.spoke_column_edit
    profile.spoke_row_edit profile.extension_margin profile.hub_margin hinner hreserve hkeep hevent hhevent
  constructor
  · intro u a c
    convert hh.1 u a c using 1 <;> ring
  · intro a ha c hc hq
    convert hh.2 a ha c hc hq using 1 <;> ring
end Oberwolfach
