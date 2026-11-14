module

public import Oberwolfach.LongRawSelectedOrdinaryMatching
public import Oberwolfach.RawOrdinaryRestrictedCandidatePhysicalLift

@[expose] public section
/-! The original raw matching gives physically disjoint rim-and-spoke
resources for all extracted ordinary wheels, even across distinct hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_selected_ordinary_physical_disjoint
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c')) →
    ∀a a':LongRawSelectedOrdinary π d m ℓ e M,a≠a'→
      Disjoint (ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val)
        (ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a').val) :=by
  intro state e R φ M hmatch a a' hne
  have hφ:Function.Injective φ:=physical_resource_to_finite_injective.comp
    (markedRawSampledPhysicalEmbedding P π d raw g j).injective
  have hdis:=long_raw_selected_ordinary_restricted_matching π d m ℓ e M hmatch a a' hne
  have ha:=raw_restricted_ordinary_candidate_physical_lift P π d _ raw g j (longRawSelectedOrdinaryWheel π d m ℓ e M a)
  have hb:=raw_restricted_ordinary_candidate_physical_lift P π d _ raw g j (longRawSelectedOrdinaryWheel π d m ℓ e M a')
  rw [←ha,←hb]
  convert (Finset.disjoint_image hφ).mpr hdis using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
end Oberwolfach
