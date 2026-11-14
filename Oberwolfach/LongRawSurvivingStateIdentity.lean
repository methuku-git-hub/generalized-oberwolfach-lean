module

public import Oberwolfach.LongRawSurvivingResourceExact
public import Oberwolfach.RawMarkedRimDeletion

@[expose] public section
/-! The filtered physical-rim state is exactly the existing raw-outcome
rim-deletion operation, with every spoke coordinate unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_surviving_state_is_raw_rim_deletion
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n))):
    longRawSurvivingResources P π d raw g j F =
      bernoulliVertexSet (longRawHubState P π d (rawMarkedDeleteRims raw F) g j):=by
  ext z
  rw [long_raw_surviving_resource_iff]
  cases z with
  | inl e =>
    cases e with
    | inl e =>
      simp [mem_bernoulliVertexSet,longRawHubState,typedMarkedResourceState,
        rawMarkedDeleteRims_rims,typedResourcePhysical,markedResourceTypeEquiv,markedPairPhysical]
    | inr e =>
      simp [mem_bernoulliVertexSet,longRawHubState,typedMarkedResourceState,
        rawMarkedDeleteRims_rims,typedResourcePhysical,markedResourceTypeEquiv,markedPairPhysical]
  | inr z =>
    rcases z with ⟨b,v,u⟩
    simp [mem_bernoulliVertexSet,longRawHubState,typedMarkedResourceState,
      rawMarkedDeleteRims_spokes,typedResourcePhysical,markedResourceTypeEquiv]
end Oberwolfach
