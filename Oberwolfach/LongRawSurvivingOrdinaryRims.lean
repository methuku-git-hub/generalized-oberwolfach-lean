module

public import Oberwolfach.LongRawSurvivingMatchingLift
public import Oberwolfach.LongRawSelectedOrdinaryRealization
public import Oberwolfach.LongRawSelectedRimPhysical

@[expose] public section
/-! The extracted ordinary rims of a lifted surviving matching avoid the
actual physical edges removed before the matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawSurvivingRimFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_surviving_ordinary_rim_avoids_deleted
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool) (F:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j F
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j F)
    let e:{z // z∈T}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    ∀a:LongRawSelectedOrdinary π d m ℓ e (M.map q),∀x y,
      longRawSelectedRimRelation π d m ℓ e (M.map q) a x y→s(x,y)∉F :=by
  intro R T S q e M a x y hrel
  let Q:=restrictedResourceSet R e
  let φ:=fun z:T=>physicalResourceToFinite (markedRawSampledPhysicalEmbedding P π d raw g j z)
  let lift:=mixedRestrictedPhysicalLift (longRawSeedResources (U:=U) π d m ℓ) e
    (longRawRealizeComponent P π d m raw g j ℓ)
  let B:=fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>
    longRawRealizedPhysicalResources P π d m raw g j ℓ z.1 z.2
  have hw:=long_raw_selected_rim_physical_resource π d m ℓ e (M.map q) a x y hrel
  have he:=long_raw_selected_ordinary_realized_resources P π d m ℓ raw g j (M.map q) a
  have he':B (lift a.val)=ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e (M.map q) a).val:=by
    convert he using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have hb:Sum.inl ({x,y}:Finset (Fin n))∈B (lift a.val):=by
    rw [he']
    convert hw using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  have hu:Sum.inl ({x,y}:Finset (Fin n))∈(M.map q).biUnion (fun c=>B (lift c)):=
    Finset.mem_biUnion.mpr ⟨a.val,a.property.1,hb⟩
  have hid:=long_raw_realized_resource_union P π d m raw g j ℓ (M.map q)
  have hid':(M.map q).biUnion (fun c=>B (lift c))=((M.map q).biUnion Q).image φ:=by
    convert hid using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  rw [hid'] at hu
  obtain ⟨z,hz,hphys⟩:=Finset.mem_image.mp hu
  obtain ⟨c,hc,hzc⟩:=Finset.mem_biUnion.mp hz
  have hzR:e z∈R c.val:=(restrictedResourceSet_mem R e c z).mp hzc
  have hp:markedRawSampledPhysicalEmbedding P π d raw g j z=Sum.inl s(x,y):=by
    apply physical_resource_to_finite_injective
    simpa [φ,physicalResourceToFinite,Sym2.toFinset_mk_eq] using hphys
  apply long_raw_lifted_matching_avoids_deleted_rims P π d m ℓ raw g j F M c hc (e z) hzR s(x,y)
  exact hp
end Oberwolfach
