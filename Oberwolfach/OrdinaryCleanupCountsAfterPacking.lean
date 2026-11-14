module

public import Oberwolfach.OrdinaryPackingPostFacts
public import Oberwolfach.OrdinaryCleanupParentCounts

@[expose] public section
/-! Both sparse-cleanup extension counts hold on the actual post-packing
host, from the earlier common profile and the same fresh sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_cleanup_counts_after_packing
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d r:ℕ)
    (X:Finset V) (Z:Finset U) (pR pH p density tR tH L βe βh t:ℝ)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (σ:Sym2 (V⊕U)→Bool)
    (profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH L βe βh s j raw)
    (hevent:OrdinaryBoundaryExtensionGood Q H X βe p σ)
    (hhevent:OrdinaryBoundaryHubPairGood H Z βh p σ)
    (M:OrdinaryUnreservedPackingData Q F H X Z (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ) r t)
    (hfacts:OrdinaryPackingPostFacts Q F H X Z (retainedGraph (ordinaryBoundaryGraph Q H X Z) σ) r t M):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    let Q':=ordinaryPackingPostRim Q F H X Z R r t M;
    let H':=ordinaryPackingPostSpokes Q F H X Z R r t M;
    (∀u a c,(p^3*βe/2)*Fintype.card (V⊕U)≤
      (((X.filter (fun v=>H' v u))∩Q'.neighborFinset a∩Q'.neighborFinset c).card:ℝ)) ∧
    (∀a∉X,∀c∉X,Q'.Adj a c→(p^2*βh/2)*Fintype.card (V⊕U)≤
      ((Z.filter (fun u=>H' a u∧H' c u)).card:ℝ)):=by
  intro R Q' H'
  have hQ:Q'≤Q:=sdiff_le
  have hkeep:ordinaryPhysicalGraph Q H\ordinaryPackingUsedGraph Q F H X Z R r t M≤ordinaryPhysicalGraph Q' H':=
    le_of_eq hfacts.exact_remainder.symm
  exact ordinary_cleanup_counts_from_parent_profile P Q Q' F H H' π d X Z
    (ordinaryPackingUsedGraph Q F H X Z R r t M) pR pH p density tR tH L βe βh s j raw σ
    profile hQ hfacts.inner_avoided hfacts.reserve_avoided hkeep hevent hhevent
end Oberwolfach
