module

public import Oberwolfach.RawOrdinarySeedPhysicalResources
public import Oberwolfach.RawMarkedRestrictedCandidatePhysicalLift

@[expose] public section
/-! The restriction of an ordinary seed retains exactly its physical
cycle and spoke resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem raw_restricted_ordinary_candidate_physical_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d r:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    let R:=fun W:OrderedOrdinaryWheel (U:=U) π (3*d) r=>
      (orderedOrdinaryResources W).map ordinaryMarkedResourceEmbedding
    ∀W:RestrictedResource R e,
      (restrictedResourceSet R e W).image (fun z=>physicalResourceToFinite (φ z))=
        ordinaryWheelPhysicalResources W.val :=by
  intro state e φ R W
  calc
    _ = ((restrictedResourceSet R e W).image e).image (markedSeedPhysicalMap π) :=by
      rw [Finset.image_image]
      rfl
    _ = (R W.val).image (markedSeedPhysicalMap π):=by rw [restrictedResourceSet_image]
    _ = ordinaryWheelPhysicalResources W.val:=ordinary_seed_physical_resource_image π (3*d) r W.val
end Oberwolfach
