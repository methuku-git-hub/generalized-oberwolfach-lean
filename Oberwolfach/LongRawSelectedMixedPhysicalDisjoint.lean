module

public import Oberwolfach.LongRawSelectedMarkedRealization
public import Oberwolfach.LongRawSelectedOrdinaryPhysicalDisjoint

@[expose] public section
/-! The original mixed matching yields physical edge-disjointness for its
extracted marked wheels and across marked/ordinary wheel types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longSelectedMixedDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_selected_mixed_physical_disjoint
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e c'))→
    (∀a a':LongRawSelectedMarked π d m ℓ e M,a≠a'→
      Disjoint (markedWheelPhysicalResources (longRawSelectedMarkedWheel P π d m ℓ raw g j M a))
        (markedWheelPhysicalResources (longRawSelectedMarkedWheel P π d m ℓ raw g j M a'))) ∧
    (∀a:LongRawSelectedMarked π d m ℓ e M,∀c:LongRawSelectedOrdinary π d m ℓ e M,
      Disjoint (markedWheelPhysicalResources (longRawSelectedMarkedWheel P π d m ℓ raw g j M a))
        (ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M c).val)):=by
  intro state e R M hmatch
  letI:∀i,Fintype (longRawSeedFamilies (U:=U) π d m ℓ i):=by
    intro i
    cases i with
    | none=>dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
    | some i=>dsimp [longRawSeedFamilies,LongMixedSeedFamily];infer_instance
  letI:∀i,DecidableEq (longRawSeedFamilies (U:=U) π d m ℓ i):=fun _=>Classical.decEq _
  let φ:=fun z=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
  let lift:=longRawRealizeComponent P π d m raw g j ℓ
  let B:=longRawRealizedPhysicalResources P π d m raw g j ℓ
  have hφ:Function.Injective φ:=physical_resource_to_finite_injective.comp
    (markedRawSampledPhysicalEmbedding P π d raw g j).injective
  have hp:∀c∈M,∀c'∈M,c≠c'→Disjoint
      (B (mixedRestrictedPhysicalLift R e lift c).1 (mixedRestrictedPhysicalLift R e lift c).2)
      (B (mixedRestrictedPhysicalLift R e lift c').1 (mixedRestrictedPhysicalLift R e lift c').2):=by
    exact (mixed_restricted_matching_physical_realizations R e φ hφ lift B
      (long_raw_realize_component_resources P π d m raw g j ℓ) M hmatch).1
  constructor
  · intro a a' hne
    have hc:a.val≠a'.val:=fun he=>hne (Subtype.ext he)
    have hh:=hp a.val a.property.1 a'.val a'.property.1 hc
    change Disjoint ((fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>B z.1 z.2) (mixedRestrictedPhysicalLift R e lift a.val))
      ((fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>B z.1 z.2) (mixedRestrictedPhysicalLift R e lift a'.val)) at hh
    rw [long_raw_selected_marked_realized_resources P π d m ℓ raw g j M a,
      long_raw_selected_marked_realized_resources P π d m ℓ raw g j M a'] at hh
    have hEq:longSelectedMixedDecEqFin n=instDecidableEqFin n:=Subsingleton.elim _ _
    rw [hEq]
    exact hh
  · intro a c
    have hc:a.val≠c.val:=by
      intro he
      have hi:=congrArg (fun z:RestrictedResource (mixedCandidateResources R) e=>z.val.1) he
      have hc:=c.property.2
      rw [a.property.2] at hi
      rw [←hi] at hc
      simp at hc
    have hh:=hp a.val a.property.1 c.val c.property.1 hc
    change Disjoint ((fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>B z.1 z.2) (mixedRestrictedPhysicalLift R e lift a.val))
      ((fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>B z.1 z.2) (mixedRestrictedPhysicalLift R e lift c.val)) at hh
    rw [long_raw_selected_marked_realized_resources P π d m ℓ raw g j M a,
      long_raw_selected_ordinary_realized_resources P π d m ℓ raw g j M c] at hh
    have hEq:longSelectedMixedDecEqFin n=instDecidableEqFin n:=Subsingleton.elim _ _
    rw [hEq]
    exact hh
end Oberwolfach
