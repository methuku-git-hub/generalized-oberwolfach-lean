module

public import Oberwolfach.MarkedActualSampleRemainingMatchingDisjoint

@[expose] public section
/-! The whole selected reference resource set is disjoint from every
approximate-layer matching of the same expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Nonempty V] [Fintype U] [DecidableEq U]

theorem marked_actual_sample_full_avoids_matching
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (z:MarkedExpandedActualOutcome (U:=U) π d):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
    let E:=MarkedSampleArc P π (3*d) (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inl e)) true
    let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun p:V×U=>H false p.1 p.2∨H true p.1 p.2))
    let raw:RawMarkedOutcome V U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let R:Type:={x // x∈bernoulliVertexSet (typedMarkedResourceState (rawMarkedPairRims P π d raw)
      (rawMarkedPairSpokes π d raw true true))}
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    ∀ (C:Type) [Fintype C] [DecidableEq C] (Qc:C→Finset R) (M:Finset C),
      Disjoint Full ((M.biUnion Qc).image (fun w=>physicalResourceToFinite (φ w))) := by
  intro H E K Full raw R φ C _ _ Qc M
  let Dempty:MarkedReferenceDeletion P π d (markedExpandedActualSelected π d z).1 := ⟨∅,∅⟩
  have hempty:Dempty.removed=∅ := by simp [Dempty,MarkedReferenceDeletion.removed,markedFiniteResources]
  have hh:=marked_actual_sample_remaining_avoids_matching P π d z Dempty C Qc M
  have hfull:Dempty.remaining H=Full:=by
    dsimp only [MarkedReferenceDeletion.remaining]
    rw [hempty,Finset.sdiff_empty]
  rw [hfull] at hh
  exact hh.symm
end Oberwolfach
