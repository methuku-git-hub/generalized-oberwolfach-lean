module

public import Oberwolfach.RawMarkedSeedCandidateLift
public import Oberwolfach.ResourceRestriction

@[expose] public section
/-! A surviving marked candidate in the sampled matching ground set lifts to
a marked wheel with precisely its original tuple and hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem raw_restricted_marked_candidate_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (raw:RawMarkedOutcome V U Γ Color)
    (g:Γ) (j:Color):
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j)
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let Parent:=MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)
    ∀W:RestrictedResource (fun W:Parent=>typedMarkedOccurrenceResources W) e,
    let E:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) false
    let K:=MarkedSampleArc P π (3*d) (fun x=>raw (Sum.inl x)) true
    let H:=rawMarkedPairSpokes π d raw g j
    ∃W':MarkedWheel (fun x:E=>x.val.1) (fun x:E=>x.val.2)
      (fun x:K=>x.val.1) (fun x:K=>x.val.2) m π (3*d) (H false) (H true),
      W'.1.val=W.val.1.val ∧ W'.2.val=W.val.2.val:=by
  intro state e Parent W E K H
  apply raw_marked_seed_candidate_lift P π d m raw g j W.val
  intro z hz
  obtain ⟨v,hv⟩:=W.property z hz
  have hh:state v.val=true:=(mem_bernoulliVertexSet state v.val).mp v.property
  simpa only [e] using hv ▸ hh
end Oberwolfach
