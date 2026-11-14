module

public import Oberwolfach.LongRawMatchingHubPacking
public import Oberwolfach.LongRawUsedEqualsOld
public import Oberwolfach.ActualWheelRimsFamilyOld
public import Oberwolfach.ActualAssignedOrdinaryRimsOld

@[expose] public section
/-! Once all selected rims occur in one source family, the exact old edge
union is the entire matching allocation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawAllRimsExactOldFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_all_rims_exact_old
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    {X A B:U→Type} [∀w,Fintype (X w)] [∀w,DecidableEq (X w)]
    [∀w,DecidableEq (A w)] [∀w,DecidableEq (B w)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool)
    (F:∀w,SimpleGraph (X w)) (data:∀w,ActualResidualData (K:=A w) (J:=B w) (F w)) (ψ:∀w,X w→Fin n):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let e:=Function.Embedding.subtype (·∈T)
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    ∀(hub:LongRawSelectedOrdinary π d m ℓ e M→U),
    (∀w,ActualWheelRimsFamilyOld (data w) (ψ w) _ _ _ _ m (3*d) π _ _ (longRawMarkedWheelsAtHub P π d m ℓ raw g j M w))→
    (∀w,ActualAssignedOrdinaryRimsOld (data w) (ψ w)
      (fun a:{a:LongRawSelectedOrdinary π d m ℓ e M // hub a=w}=>ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a.val).1)
      (fun a=>(longRawSelectedOrdinaryWheel π d m ℓ e M a.val).val.1.val))→
    let old:=fun w=>((data w).deletedEdges\(Finset.univ.biUnion
      (fun i:{i // i∈(data w).s₁}=>((data w).path (.inl i)).edges.toFinset))).image (Sym2.map (ψ w))
    let Pack:=Finset.univ.biUnion old
    Pack⊆(physicalRimCandidateUnion (markedRawSampledPhysicalEmbedding P π d raw g j)
      (restrictedResourceSet (mixedCandidateResources R) e) M).edgeFinset→
    Pack=(physicalRimCandidateUnion (markedRawSampledPhysicalEmbedding P π d raw g j)
      (restrictedResourceSet (mixedCandidateResources R) e) M).edgeFinset:=by
  intro T e R M hub hMarked hOrd old Pack hsub
  apply long_raw_used_equals_old P π d m ℓ raw g j Pack M hsub
  · intro a edge hedge
    let W:=longRawSelectedMarkedWheel P π d m ℓ raw g j M a
    let w:=W.2.val
    have hmem:W∈longRawMarkedWheelsAtHub P π d m ℓ raw g j M w:=by
      apply Finset.mem_image.mpr
      exact ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩
    obtain ⟨b,hb,heq⟩:=hMarked w W hmem edge.toFinset hedge
    have hab:b=edge:=sym2_toFinset_injective_local heq
    apply Finset.mem_biUnion.mpr
    exact ⟨w,Finset.mem_univ _,hab ▸ hb⟩
  · intro a k
    apply Finset.mem_biUnion.mpr
    refine ⟨hub a,Finset.mem_univ _,?_⟩
    exact hOrd (hub a) ⟨a,rfl⟩ k
end Oberwolfach
