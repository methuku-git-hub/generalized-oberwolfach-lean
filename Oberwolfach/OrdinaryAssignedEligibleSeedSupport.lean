module

public import Oberwolfach.OrdinaryAssignedNamedSeeds
public import Oberwolfach.OrdinaryEligibleSeedSupport

@[expose] public section
/-! The named factor-assigned seeds are supported on eligible physical
resources when their fixed parent weights use the eligible host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedEligibleSupportFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_assigned_eligible_shifted_seed_support
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c D:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (τ A BM:ℝ) (weight:(Fin (m+1)→Fin n)→ℝ)
    (hw:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ A BM weight):
    ∀W,ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m weight W≠0→
      ∀z∈typedMarkedOccurrenceResources W,ordinaryPhysicalEligible (U:=U) π d (ordinaryMixedPhysicalResource π z) :=by
  simpa only [ordinaryAssignedShiftedSeed] using ordinary_eligible_shifted_seed_support P π d m D τ A BM
    (ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D)
    (ordinaryAssignedShortWeight F hF K i₀ rsv θ c) weight hw

theorem ordinary_assigned_eligible_unshifted_seed_support
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ c D:ℝ) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (weight:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ):
    ∀i W,ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d weight i W≠0→
      ∀z∈(orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding,
        ordinaryPhysicalEligible (U:=U) π d (ordinaryMixedPhysicalResource π z) :=by
  intro i
  simpa only [ordinaryAssignedUnshiftedSeed] using ordinary_eligible_unshifted_seed_support P π d
    (longPaddedSeedExponent i) (long_padded_seed_exponent_positive i) D
    (ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D)
    (ordinaryAssignedShortWeight F hF K i₀ rsv θ c)
    (fun u=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c u i) (weight i)
end Oberwolfach
