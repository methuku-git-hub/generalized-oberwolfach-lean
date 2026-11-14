module

public import Oberwolfach.RawMarkedSeedCandidateLift
public import Oberwolfach.RawMatchingAvoidsSelectedAbsorber
public import Oberwolfach.MarkedWheelRestriction

@[expose] public section
/-! The typed resources of a marked seed map to exactly its physical wheel
resources, including the permutation-twisted closing edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]

def markedSeedPhysicalMap (π:Equiv.Perm V):
    (((V×V)⊕(V×V))⊕(Bool×V×U))→(Finset V⊕(V×U)):=
  fun z=>physicalResourceToFinite (typedResourcePhysical π (markedResourceTypeEquiv z))

theorem marked_seed_physical_map_rim (π:Equiv.Perm V) (a:(V×V)⊕(V×V)):
    markedSeedPhysicalMap (U:=U) π (Sum.inl a)=
      Sum.inl (markedPhysicalEdge (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd π a):=by
  cases a <;> simp [markedSeedPhysicalMap,physicalResourceToFinite,typedResourcePhysical,
    markedResourceTypeEquiv,markedPhysicalEdge,Sym2.toFinset_mk_eq]

theorem marked_seed_physical_map_spoke (π:Equiv.Perm V) (b:Bool) (v:V) (u:U):
    markedSeedPhysicalMap π (Sum.inr (b,v,u))=Sum.inr (v,u):=by rfl

theorem marked_seed_physical_resource_image
    (π:Equiv.Perm V) (m b:ℕ)
    (W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)):
    (typedMarkedOccurrenceResources W).image (markedSeedPhysicalMap π)=markedWheelPhysicalResources W :=by
  ext z
  cases z with
  | inl edge=>
    simp only [Finset.mem_image,typedMarkedOccurrenceResources,Finset.mem_union,Finset.mem_image,
      Finset.mem_filter,Finset.mem_univ,true_and,markedWheelPhysicalResources_rim,
      markedCyclePhysicalEdges,Sum.inl.injEq]
    constructor
    · rintro ⟨r,hr,hrz⟩
      rcases hr with ⟨a,ha,rfl⟩|⟨i,rfl⟩
      · rw [marked_seed_physical_map_rim] at hrz
        obtain ⟨i,hi⟩:=ha
        refine ⟨i,?_⟩
        have hh:markedPhysicalEdge (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd π a=edge:=Sum.inl.inj hrz
        simpa only [Function.comp_apply,hi] using hh
      · simp [marked_seed_physical_map_spoke] at hrz
    · rintro ⟨i,hi⟩
      let a:=markedCycleTypedEdge (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b W.1 i
      refine ⟨Sum.inl a,Or.inl ⟨a,⟨i,rfl⟩,rfl⟩,?_⟩
      rw [marked_seed_physical_map_rim]
      exact congrArg Sum.inl hi
  | inr vu=>
    rcases vu with ⟨v,u⟩
    simp only [Finset.mem_image,typedMarkedOccurrenceResources,Finset.mem_union,Finset.mem_image,
      Finset.mem_filter,Finset.mem_univ,true_and,markedWheelPhysicalResources_spoke]
    constructor
    · rintro ⟨r,hr,hrz⟩
      rcases hr with ⟨a,ha,rfl⟩|⟨i,rfl⟩
      · simp [marked_seed_physical_map_rim] at hrz
      · simp only [marked_seed_physical_map_spoke,Sum.inr.injEq,Prod.mk.injEq] at hrz
        exact ⟨hrz.2,i,hrz.1⟩
    · rintro ⟨hu,i,hi⟩
      refine ⟨Sum.inr (decide (i=0),W.1.val i,W.2.val),Or.inr ⟨i,rfl⟩,?_⟩
      simp only [marked_seed_physical_map_spoke,Sum.inr.injEq,Prod.mk.injEq]
      exact ⟨hi,hu⟩
end Oberwolfach
