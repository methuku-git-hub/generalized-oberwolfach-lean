module

public import Oberwolfach.LongActualMixedRealizationsSampleDisjoint
public import Oberwolfach.LongRawRealizationsAvoidAbsorber

@[expose] public section
/-! The marked and ordinary wheel realizations of an approximate mixed
matching avoid all selected reference resources on the same outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance actualMixedRealizationsRemainderFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

theorem long_actual_mixed_realizations_avoid_reference_remainder
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d)
    (D₀:MarkedReferenceDeletion P π d (markedExpandedActualSelected π d z).1):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
    let E:=MarkedSampleArc P π (3*d) (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inl e)) false
    let Kedge:=MarkedSampleArc P π (3*d) (fun e=>(markedExpandedActualSelected π d z).1 (Sum.inl e)) true
    let Full:=markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:Kedge=>e.val.1) (fun e=>e.val.2) π Finset.univ
      (Finset.univ.filter (fun p:Fin n×U=>H false p.1 p.2∨H true p.1 p.2))
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (z.1 e)
    let state:=typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw true true)
    let e:{v // v∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw true true ℓ)
    let B:=longRawRealizedPhysicalResources P π d m raw true true ℓ;
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
      Disjoint (D₀.remaining H) (M.biUnion (fun c=>B (lift c).1 (lift c).2)) := by
  intro H E Kedge Full raw state e R lift B M
  have h:=long_actual_mixed_realizations_avoid_reference_sample P π d m ℓ z M
  have hsub:D₀.remaining H⊆Full:=by
    dsimp only [MarkedReferenceDeletion.remaining,Full]
    exact Finset.sdiff_subset
  exact Finset.disjoint_of_subset_left hsub h
end Oberwolfach
