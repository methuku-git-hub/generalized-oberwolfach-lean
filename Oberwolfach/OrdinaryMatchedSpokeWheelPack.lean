module

public import Oberwolfach.OrdinaryPhysicalCandidateSpokeHub
public import Oberwolfach.OrdinaryMarkedTupleVertexInRim

@[expose] public section

/-! A covered physical spoke belongs to the rim-vertex set of one of the
same hub's wheels in the coherent matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_matched_spoke_in_wheel_pack
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state)) (u:U)
    (W:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
      (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀a,(W a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W a).2.val=u),
    let len:=fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>
      longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2
    let Q:=fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>
      (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2
    let Pack:=mixedWheelRimPack len (Finset.univ.image W) Q;
    ∀(c:PhysicalSampledCandidate (mixedCandidateResources RR) state),c∈L→
    ∀(x:PhysicalSampledActive φ state) (v:Fin n),x.val=Sum.inr (v,u)→
      x∈physicalSampledCandidateSet φ (mixedCandidateResources RR) state c→
      ∃edge∈Pack,v∈edge :=by
  intro RM state RR φ L u W hW len Q Pack c hc x v hx hcx
  have hhub:=ordinary_physical_candidate_spoke_hub (K:=K) π d m Rim H c x v u hx hcx
  have hm:x.val∈(mixedCandidateResources RR c.val).image φ:=
    (physical_sampled_candidate_set_mem φ (mixedCandidateResources RR) state c x).mp hcx
  obtain ⟨a,ha,he⟩:=Finset.mem_image.mp hm
  have hphys:Sum.inr (v,u)∈(mixedCandidateResources RR c.val).image (markedSeedPhysicalMap π):=by
    apply Finset.mem_image.mpr
    refine ⟨a,ha,?_⟩
    rw [←ordinary_physical_resource_to_finite_comp π]
    change ordinaryPhysicalResourceToFinite (φ a)=Sum.inr (v,u)
    rw [he,hx]
    rfl
  by_cases hnone:c.val.1.isNone
  · let z:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u:=
      ⟨c,Finset.mem_filter.mpr ⟨hc,hnone,hhub⟩⟩
    have hres:=ordinary_physical_marked_payload_finite_resources (K:=K) π d m Rim H L u z
    change Sum.inr (v,u)∈(mixedCandidateResources RR z.val.val).image (markedSeedPhysicalMap π) at hphys
    rw [hres] at hphys
    obtain ⟨_,hvertices⟩:=(markedWheelPhysicalResources_spoke (ordinaryPhysicalMarkedRefinement π d m Rim H L u z) v u).mp hphys
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hvertices
    have hvi:(W z).1.val i=v:=by
      rw [(hW z).1]
      exact hi
    obtain ⟨edge,hedge,hv⟩:=ordinary_marked_tuple_vertex_in_rim _ _ _ _ m π (3*d) (W z).1 i
    refine ⟨edge,?_,?_⟩
    · simp only [Pack,mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion]
      refine Or.inl ⟨W z,Finset.mem_image.mpr ⟨z,Finset.mem_univ _,rfl⟩,?_⟩
      convert hedge using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
    · simpa only [hvi] using hv
  · have hsome:c.val.1.isSome:=by cases hh:c.val.1 <;> simp_all
    let z:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u:=
      ⟨c,Finset.mem_filter.mpr ⟨hc,hsome,hhub⟩⟩
    have hres:=ordinary_physical_unmarked_payload_finite_resources (K:=K) π d m Rim H L u z
    change Sum.inr (v,u)∈(mixedCandidateResources RR z.val.val).image (markedSeedPhysicalMap π) at hphys
    rw [hres] at hphys
    have hex:∃i,(Q z).1.val i=v ∧ (Q z).2=u:=by
      simpa [Q,ordinaryWheelPhysicalResources] using hphys
    obtain ⟨i,hi,_⟩:=hex
    let edge:Finset (Fin n):={(Q z).1.val i,(Q z).1.val (cycleNext i)}
    refine ⟨edge,?_,?_⟩
    · simp only [Pack,mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
      refine Or.inr ⟨z,i,?_⟩
      ext y
      simp [edge]
    · simp [edge,hi]
end Oberwolfach
