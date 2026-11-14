module

public import Oberwolfach.OrdinaryUnreservedPackingFixedCut
public import Oberwolfach.OrdinarySampledCleanupAfterPacking

@[expose] public section
/-! Per-outcome assumptions for coupling unreserved packing and sparse
cleanup on one common and fresh sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

structure OrdinaryPackingCleanupSampleInputs (r:ℕ) (hr:3≤r) (k d:ℕ)
    (α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε b c:ℝ)
    (pR pH density tR tH Ledit βe βh L:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (X:Finset V) (Z:Finset U)
    (s:U→Color→ℝ) (j:Color) (raw:RawWheelOutcome V U Γ Color) (σ:Sym2 (V⊕U)→Bool):Prop where
  parent:Nonempty (OrdinaryUnreservedParentData r hr k α ω β₀ β bminus bplus h δ
    ε₀ εstar η ξ ζ p ε b c P Q F H X Z σ)
  cleanup_profile:OrdinaryCleanupParentProfiles P Q F H π d X Z pR pH density tR tH Ledit βe βh s j raw
  conflict_degree:∀v,(F.degree v:ℝ)≤L
  balanced:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card
  divisible:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card
  extensions:OrdinaryBoundaryExtensionGood Q H X βe p σ
  hub_pairs:OrdinaryBoundaryHubPairGood H Z βh p σ
end Oberwolfach
