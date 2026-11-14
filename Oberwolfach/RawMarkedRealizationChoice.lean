module

public import Oberwolfach.RawMarkedRestrictedCandidatePhysicalLift

@[expose] public section
/-! Choose a realization while preserving the original tuple and hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

def rawMarkedRealization
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let Parent:=MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)
    let R:=fun W:Parent=>typedMarkedOccurrenceResources W
    let E:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) false
    let K:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) true
    let H:=rawMarkedPairSpokes π d raw g j
    RestrictedResource R e→MarkedWheel (fun x:E=>x.val.1) (fun x:E=>x.val.2)
      (fun x:K=>x.val.1) (fun x:K=>x.val.2) m π (3*d) (H false) (H true) :=by
  intro state e Parent R E K H W
  exact Classical.choose (raw_restricted_marked_candidate_physical_lift P π d m raw g j W)

theorem raw_marked_realization_properties
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    let Parent:=MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)
    let R:=fun W:Parent=>typedMarkedOccurrenceResources W
    ∀W:RestrictedResource R e,
      (rawMarkedRealization P π d m raw g j W).1.val=W.val.1.val ∧
      (rawMarkedRealization P π d m raw g j W).2.val=W.val.2.val ∧
      (restrictedResourceSet R e W).image (fun z=>physicalResourceToFinite (φ z))=
        markedWheelPhysicalResources (rawMarkedRealization P π d m raw g j W) :=by
  intro state e φ Parent R W
  exact Classical.choose_spec (raw_restricted_marked_candidate_physical_lift P π d m raw g j W)
end Oberwolfach
