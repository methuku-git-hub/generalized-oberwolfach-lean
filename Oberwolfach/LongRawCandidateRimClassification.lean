module

public import Oberwolfach.LongRawRealizationsAvoidAbsorber
public import Oberwolfach.LongRawSelectedMarkedRealization
public import Oberwolfach.LongRawSelectedOrdinaryRealization
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! Every used matching edge belongs to a selected marked or ordinary wheel
of the same matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawCandidateRimClassFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_candidate_rim_classification
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let e:=Function.Embedding.subtype (·∈T)
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    let Used:=physicalRimCandidateUnion φ (restrictedResourceSet (mixedCandidateResources R) e) M;
    ∀x y,Used.Adj x y→
      (∃a:LongRawSelectedMarked π d m ℓ e M,
        s(x,y).toFinset∈markedCyclePhysicalEdges _ _ _ _ m π (3*d) (longRawSelectedMarkedWheel P π d m ℓ raw g j M a).1) ∨
      (∃a:LongRawSelectedOrdinary π d m ℓ e M,∃k,
        s(x,y).toFinset={((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val k),
          ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val (cycleNext k))}):=by
  intro T e R φ M Used x y hxy
  change x≠y ∧ ∃c∈M,∃z∈restrictedResourceSet (mixedCandidateResources R) e c,φ z=Sum.inl s(x,y) at hxy
  obtain ⟨_,c,hc,z,hz,hφ⟩:=hxy
  let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ)
  let B:=longRawRealizedPhysicalResources P π d m raw g j ℓ
  have hres:Sum.inl s(x,y).toFinset∈M.biUnion (fun c=>B (lift c).1 (lift c).2):=by
    have hu:=long_raw_realized_resource_union P π d m raw g j ℓ M
    have hu' : (M.biUnion (fun c=>B (lift c).1 (lift c).2))=
        (M.biUnion (restrictedResourceSet (mixedCandidateResources R) e)).image (fun z=>physicalResourceToFinite (φ z)):=by
      convert hu using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    rw [hu']
    refine Finset.mem_image.mpr ⟨z,Finset.mem_biUnion.mpr ⟨c,hc,hz⟩,?_⟩
    simp only [hφ,physicalResourceToFinite,Sum.map_inl]
  obtain ⟨c,hc,hres⟩:=Finset.mem_biUnion.mp hres
  cases hidx:c.val.1 with
  | none =>
    let a:LongRawSelectedMarked π d m ℓ e M:=⟨c,hc,hidx⟩
    have heq:=long_raw_selected_marked_realized_resources P π d m ℓ raw g j M a
    have heq':B (lift c).1 (lift c).2=markedWheelPhysicalResources (longRawSelectedMarkedWheel P π d m ℓ raw g j M a):=by
      convert heq using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    rw [heq'] at hres
    left
    exact ⟨a,(markedWheelPhysicalResources_rim _ _).mp hres⟩
  | some k =>
    let a:LongRawSelectedOrdinary π d m ℓ e M:=⟨c,hc,by rw [hidx];rfl⟩
    have heq:=long_raw_selected_ordinary_realized_resources P π d m ℓ raw g j M a
    have heq':B (lift c).1 (lift c).2=ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val:=by
      convert heq using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    rw [heq'] at hres
    right
    unfold ordinaryWheelPhysicalResources at hres
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and,Sum.inr_ne_inl,exists_false,or_false,Sum.inl.injEq] at hres
    obtain ⟨i,hi⟩:=hres
    exact ⟨a,i,hi.symm⟩
end Oberwolfach
