module

public import Oberwolfach.MarkedActualSampleFullMatchingDisjoint
public import Oberwolfach.RestrictedResourceStateLift

@[expose] public section
/-! A matching in a surviving approximate resource set remains disjoint from
the whole selected reference sample after the canonical resource embedding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

theorem marked_actual_surviving_matching_avoids_sample
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (z:MarkedExpandedActualOutcome (U:=U) π d):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
    let E:=MarkedSampleArc P π (3*d) (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inl e)) true
    let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun p:V×U=>H false p.1 p.2∨H true p.1 p.2))
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let T:=bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw true true))
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    ∀ (S:Finset _) (hST:S⊆T),
    let f:=survivingResourceEmbedding S T hST;
    ∀ (C:Type) [Fintype C] [DecidableEq C] (Qc:C→Finset S) (M:Finset C),
      Disjoint Full ((M.biUnion Qc).image (fun w=>physicalResourceToFinite (φ (f w)))) := by
  intro H E K Full raw T φ S hST f C _ _ Qc M
  let Qc':C→Finset T:=fun c=>(Qc c).image f
  have h:=marked_actual_sample_full_avoids_matching P π d z C Qc' M
  have heq:(M.biUnion Qc').image (fun w=>physicalResourceToFinite (φ w))=
      (M.biUnion Qc).image (fun w=>physicalResourceToFinite (φ (f w))) := by
    ext x
    simp only [Finset.mem_image,Finset.mem_biUnion,Qc']
    constructor
    · rintro ⟨y,⟨c,hc,w,hw,rfl⟩,hy⟩
      exact ⟨w,⟨c,hc,hw⟩,hy⟩
    · rintro ⟨w,⟨c,hc,hw⟩,hy⟩
      exact ⟨f w,⟨c,hc,w,hw,rfl⟩,hy⟩
  rw [heq] at h
  exact h
end Oberwolfach
