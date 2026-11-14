module

public import Oberwolfach.LongActualMixedRemainderDecomposition
public import Oberwolfach.LongRawSurvivingMatchingLift
public import Oberwolfach.LongActualMixedRealizationsRemainderDisjoint
public import Oberwolfach.ResourceSumDecomposition
public import Oberwolfach.LongRawSelectedMixedPhysicalDisjoint
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
local instance actualSurvivingMixedDecompositionFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]

theorem long_actual_surviving_mixed_matching_and_reference_remainder_decomposition
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (z:MarkedExpandedActualOutcome (U:=U) π d) (Del:SimpleGraph (Fin n))
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
    let T:=bernoulliVertexSet state
    let S:=longRawSurvivingResources P π d raw true true Del.edgeFinset
    let e:{v // v∈T}↪_:=Function.Embedding.subtype _
    let eS:{v // v∈S}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let q:=survivingCandidateEmbedding (mixedCandidateResources R) S T
      (long_raw_surviving_resources_subset P π d raw true true Del.edgeFinset)
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw true true ℓ)
    let B:=longRawRealizedPhysicalResources P π d m raw true true ℓ
    let Wref:=MarkedWheel (fun x:E=>x.val.1) (fun x=>x.val.2)
      (fun x:Kedge=>x.val.1) (fun x=>x.val.2) m π (3*d) (H false) (H true)
    let Wmix:=Σi,LongRawRealizedWheel P π d m raw true true ℓ i
    let Rref:Wref→Finset (Finset (Fin n)⊕(Fin n×U)):=fun w=>markedWheelPhysicalResources w
    let Rmix:Wmix→Finset (Finset (Fin n)⊕(Fin n×U)):=fun w=>B w.1 w.2;
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) eS),
    (∀c∈M,∀c'∈M,c≠c'→Disjoint (restrictedResourceSet (mixedCandidateResources R) eS c)
      (restrictedResourceSet (mixedCandidateResources R) eS c')) →
    HasResourceDecomposition Rref (D₀.remaining H) →
    HasResourceDecomposition (Sum.elim Rref Rmix) ((D₀.remaining H)∪(M.map q).biUnion (fun c=>Rmix (lift c))) := by
  intro H E Kedge Full raw state T S e eS R q lift B Wref Wmix Rref Rmix M hmatch hdec
  have hFinEq:actualSurvivingMixedDecompositionFinDecidable n=instDecidableEqFin n:=Subsingleton.elim _ _
  have hmatch':=hmatch
  rw [hFinEq] at hmatch'
  have hlift:=(long_raw_surviving_matching_lift P π d m ℓ raw true true Del.edgeFinset M hmatch').1
  rw [←hFinEq] at hlift
  exact long_actual_mixed_matching_and_reference_remainder_decomposition P π d m ℓ z D₀ (M.map q) hlift hdec
end Oberwolfach
