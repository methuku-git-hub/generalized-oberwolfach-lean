module

public import Oberwolfach.MarkedActualSurvivingMatchingDisjoint
public import Oberwolfach.LongRawSurvivingCandidateExact

@[expose] public section
/-! The actual surviving mixed-candidate matching avoids the complete
retained reference sample on the same expanded outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance actualMixedReferenceFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

theorem long_actual_mixed_matching_avoids_reference_sample
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Del:SimpleGraph (Fin n)):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
    let E:=MarkedSampleArc P π (3*d) (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inl e)) false
    let Kedge:=MarkedSampleArc P π (3*d) (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inl e)) true
    let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:Kedge=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun p:Fin n×U=>H false p.1 p.2∨H true p.1 p.2))
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let R:=longRawHubResources (U:=U) π d m ℓ
    let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let e:S↪LongRawHubResource n U:=Function.Embedding.subtype _
    let Cand:=RestrictedResource (mixedCandidateResources R) e
    let Q:=restrictedResourceSet (mixedCandidateResources R) e
    let fS:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw true true;
    ∀M:Finset Cand,
      Disjoint Full ((M.biUnion Q).image (fun w=>physicalResourceToFinite (φ (fS w)))) := by
  intro H E Kedge Full raw R S T e Cand Q fS φ M
  exact marked_actual_surviving_matching_avoids_sample P π d z S
    (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset) Cand Q M
end Oberwolfach
