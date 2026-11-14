module

public import Oberwolfach.LongMixedRawWheelBase

@[expose] public section
/-! Transfer the restrictions of each mixed-family component while
retaining precisely the same set of active typed resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longMixedRestrictedComponentsDecidableEqFin1 (n:ℕ) : DecidableEq (Fin n) := Classical.decEq _
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

def longRawMarkedComponent (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (W:RestrictedResource (longRawSeedResources (U:=U) π d m ℓ none) e):
    RestrictedResource (fun C:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources C) e:=by
  refine ⟨W.val,?_⟩
  intro v hv
  apply W.property v
  simpa only [longRawSeedResources,longMixedSeedResources,typedMarkedOccurrenceResources,
    Finset.mem_union,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and] using hv

theorem long_raw_marked_component_resources (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (W:RestrictedResource (longRawSeedResources (U:=U) π d m ℓ none) e):
    restrictedResourceSet (longRawSeedResources (U:=U) π d m ℓ none) e W =
      restrictedResourceSet (fun C:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π (3*d)
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources C) e
          (longRawMarkedComponent π d m ℓ e W):=by
  ext x
  simp only [restrictedResourceSet,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [longRawSeedResources,longMixedSeedResources,
    longRawMarkedComponent,typedMarkedOccurrenceResources,Finset.mem_union,Finset.mem_image,
    Finset.mem_filter,Finset.mem_univ,true_and]

def longRawOrdinaryComponent (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (i:Fin K)
    (e:X↪(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (W:RestrictedResource (longRawSeedResources (U:=U) π d m ℓ (some i)) e):
    RestrictedResource (fun C:OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ i)=>
      (orderedOrdinaryResources C).map ordinaryMarkedResourceEmbedding) e:=by
  refine ⟨W.val,?_⟩
  intro v hv
  apply W.property v
  simpa only [longRawSeedResources,longMixedSeedResources,Finset.mem_map,
    orderedOrdinaryResources,Finset.mem_union,Finset.mem_image] using hv

theorem long_raw_ordinary_component_resources (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (i:Fin K)
    (e:X↪(((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)))
    (W:RestrictedResource (longRawSeedResources (U:=U) π d m ℓ (some i)) e):
    restrictedResourceSet (longRawSeedResources (U:=U) π d m ℓ (some i)) e W =
      restrictedResourceSet (fun C:OrderedOrdinaryWheel (U:=U) π (3*d) (ℓ i)=>
        (orderedOrdinaryResources C).map ordinaryMarkedResourceEmbedding) e
          (longRawOrdinaryComponent π d m ℓ i e W):=by
  ext x
  simp only [restrictedResourceSet,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [longRawSeedResources,longMixedSeedResources,longRawOrdinaryComponent,
    Finset.mem_map,orderedOrdinaryResources,Finset.mem_union,Finset.mem_image]
end Oberwolfach
