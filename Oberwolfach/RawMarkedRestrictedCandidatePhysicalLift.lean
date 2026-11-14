module

public import Oberwolfach.RawMarkedRestrictedCandidateLift
public import Oberwolfach.RawMarkedSeedPhysicalResources
public import Oberwolfach.MarkedWheelTuplePhysicalInvariant

@[expose] public section
/-! A sampled marked candidate lifts to an actual wheel with exactly the
physical resources represented by its typed matching resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem raw_restricted_marked_candidate_physical_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    let Parent:=MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)
    let R:=fun W:Parent=>typedMarkedOccurrenceResources W
    ∀W:RestrictedResource R e,
    let E:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) false
    let K:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) true
    let H:=rawMarkedPairSpokes π d raw g j
    ∃W':MarkedWheel (fun x:E=>x.val.1) (fun x:E=>x.val.2)
      (fun x:K=>x.val.1) (fun x:K=>x.val.2) m π (3*d) (H false) (H true),
      W'.1.val=W.val.1.val ∧ W'.2.val=W.val.2.val ∧
      (restrictedResourceSet R e W).image (fun z=>physicalResourceToFinite (φ z))=
        markedWheelPhysicalResources W' :=by
  intro state e φ Parent R W E K H
  obtain ⟨W',htuple,hhub⟩:=raw_restricted_marked_candidate_lift P π d m raw g j W
  refine ⟨W',htuple,hhub,?_⟩
  calc
    _ = ((restrictedResourceSet R e W).image e).image (markedSeedPhysicalMap π) :=by
      rw [Finset.image_image]
      rfl
    _ = (R W.val).image (markedSeedPhysicalMap π):=by rw [restrictedResourceSet_image]
    _ = markedWheelPhysicalResources W.val:=marked_seed_physical_resource_image π m (3*d) W.val
    _ = markedWheelPhysicalResources W':=(marked_wheel_same_tuple_same_physical_resources W.val W' htuple hhub).symm
end Oberwolfach
