module

public import Oberwolfach.OrdinaryPhysicalPayloadFiniteResources
public import Oberwolfach.OrdinaryPhysicalMatchingNamedWheelFamily
public import Oberwolfach.MixedWheelRimPacksDisjoint

@[expose] public section
/-! Every physical rim resource covered by the selected mixed matching is
in the rim pack of the wheel's own hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem ordinary_matching_packs_cover_physical_rims {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (Rim:(Fin n×Fin n)⊕(Fin n×Fin n)→Prop) (H:Bool→Fin n→U→Prop):
    let RM:=fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W
    let state:=typedMarkedResourceState Rim H
    let RR:=ordinaryMixedGenericResources RM (fun (i:Fin K) (W:OrderedOrdinaryWheel (U:=U) π (3*d) (longPaddedSeedExponent i+2))=>orderedOrdinaryResources W)
    let φ:=ordinaryMixedPhysicalResource (U:=U) π;
    ∀(L:Finset (PhysicalSampledCandidate (mixedCandidateResources RR) state))
    (W:∀u,OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u→
      MarkedWheel (fun e:{e:Fin n×Fin n // Rim (Sum.inl e)}=>e.val.1) (fun e=>e.val.2)
        (fun e:{e:Fin n×Fin n // Rim (Sum.inr e)}=>e.val.1) (fun e=>e.val.2) m π (3*d) (H false) (H true))
    (hW:∀u a,(W u a).1.val=(ordinaryPhysicalMarkedPayload π d m RM state L u a).1.val ∧ (W u a).2.val=u),
    let Pack:=fun u=>mixedWheelRimPack
      (fun a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u=>longPaddedSeedExponent (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).1+2)
      (Finset.univ.image (W u)) (fun a=>(ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2);
    ∀c∈L,∀z∈physicalSampledCandidateSet φ (mixedCandidateResources RR) state c,
      ∀e:Sym2 (Fin n),z.val=Sum.inl e→∃u,e.toFinset∈Pack u:=by
  intro RM state RR φ L W hW Pack c hc z hz e he
  let u:=ordinaryMixedGenericWheelHub (U:=U) π (3*d) m longPaddedSeedExponent c.val.1 c.val.2
  have hres:z.val∈(mixedCandidateResources RR c.val).image φ:=
    (physical_sampled_candidate_set_mem φ (mixedCandidateResources RR) state c z).mp hz
  have hfinite:Sum.inl e.toFinset∈(mixedCandidateResources RR c.val).image (markedSeedPhysicalMap π):=by
    have hh:=Finset.mem_image_of_mem (ordinaryPhysicalResourceToFinite (V:=Fin n) (U:=U)) hres
    rw [Finset.image_image,ordinary_physical_resource_to_finite_comp π] at hh
    simp only [he,ordinaryPhysicalResourceToFinite,Sum.map_inl] at hh
    convert hh using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  cases htag:c.val.1 with
  | none=>
    let a:OrdinaryPhysicalMarkedHub (K:=K) π d m RM state L u:=
      ⟨c,Finset.mem_filter.mpr ⟨hc,by simp [htag],rfl⟩⟩
    have hh:=ordinary_physical_marked_payload_finite_resources (K:=K) π d m Rim H L u a
    have hfinite':Sum.inl e.toFinset∈markedWheelPhysicalResources (ordinaryPhysicalMarkedRefinement π d m Rim H L u a):=by
      rw [←hh]
      exact hfinite
    have htuple:(W u a).1.val=(ordinaryPhysicalMarkedRefinement π d m Rim H L u a).1.val:=(hW u a).1
    have hhub:(W u a).2.val=(ordinaryPhysicalMarkedRefinement π d m Rim H L u a).2.val:=by
      rw [(hW u a).2]
      exact (ordinary_physical_marked_payload_hub π d m RM state L u a).symm
    have heq:=marked_wheel_same_tuple_same_physical_resources (ordinaryPhysicalMarkedRefinement π d m Rim H L u a) (W u a) htuple hhub
    have hmark:Sum.inl e.toFinset∈markedWheelPhysicalResources (W u a):=by rw [heq];exact hfinite'
    refine ⟨u,?_⟩
    simp only [Pack,mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
    left
    refine ⟨W u a,⟨a,rfl⟩,?_⟩
    convert (markedWheelPhysicalResources_rim (W u a) e.toFinset).mp hmark using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  | some i=>
    let a:OrdinaryPhysicalUnmarkedHub (K:=K) π d m RM state L u:=
      ⟨c,Finset.mem_filter.mpr ⟨hc,by simp [htag],rfl⟩⟩
    have hh:=ordinary_physical_unmarked_payload_finite_resources (K:=K) π d m Rim H L u a
    have hfinite':Sum.inl e.toFinset∈ordinaryWheelPhysicalResources (ordinaryPhysicalUnmarkedPayload π d m RM state L u a).2:=by
      rw [←hh]
      exact hfinite
    simp only [ordinaryWheelPhysicalResources,Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hfinite'
    rcases hfinite' with ⟨j,hj⟩|⟨j,hj⟩
    · refine ⟨u,?_⟩
      simp only [Pack,mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
      right
      exact ⟨a,j,Sum.inl.inj hj⟩
    · cases hj
end Oberwolfach
