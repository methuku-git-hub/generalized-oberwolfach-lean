module

public import Oberwolfach.MixedRestrictedFamilyEquiv
public import Oberwolfach.MatchingPhysicalLift

@[expose] public section
/-! Assemble physical realizations of separate indexed families without
changing the sampled resource sets or candidate identifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V X Y:Type} [Fintype I] [Fintype V] [Fintype X] [DecidableEq I]
  [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_restricted_component_resources
    (R:∀i,E i→Finset V) (e:X↪V)
    (c:RestrictedResource (mixedCandidateResources R) e):
    restrictedResourceSet (mixedCandidateResources R) e c =
      restrictedResourceSet (R c.val.1) e ((mixedRestrictedFamilyEquiv R e c).2) :=by
  ext x
  simp only [restrictedResourceSet_mem,mixedCandidateResources,mixedRestrictedFamilyEquiv]
  rfl

def mixedRestrictedPhysicalLift (R:∀i,E i→Finset V) (e:X↪V)
    {W:I→Type} (lift:∀i,RestrictedResource (R i) e→W i)
    (c:RestrictedResource (mixedCandidateResources R) e):Σi,W i :=
  ⟨c.val.1,lift c.val.1 ((mixedRestrictedFamilyEquiv R e c).2)⟩

theorem mixed_restricted_physical_lift_resources
    (R:∀i,E i→Finset V) (e:X↪V) (φ:X→Y) {W:I→Type}
    (lift:∀i,RestrictedResource (R i) e→W i) (B:∀i,W i→Finset Y)
    (h:∀i c,B i (lift i c)=(restrictedResourceSet (R i) e c).image φ)
    (c:RestrictedResource (mixedCandidateResources R) e):
    B (mixedRestrictedPhysicalLift R e lift c).1 (mixedRestrictedPhysicalLift R e lift c).2 =
      (restrictedResourceSet (mixedCandidateResources R) e c).image φ :=by
  rw [mixed_restricted_component_resources]
  exact h _ _
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V X Y:Type} [Fintype I] [Fintype V] [Fintype X] [DecidableEq I]
  [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_restricted_matching_physical_realizations
    (R:∀i,E i→Finset V) (e:X↪V) (φ:X→Y) (hφ:Function.Injective φ) {W:I→Type}
    (lift:∀i,RestrictedResource (R i) e→W i) (B:∀i,W i→Finset Y)
    (h:∀i c,B i (lift i c)=(restrictedResourceSet (R i) e c).image φ)
    (S:Finset (RestrictedResource (mixedCandidateResources R) e))
    (hmatch:∀c∈S,∀d∈S,c≠d→Disjoint
      (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e d)):
    (∀c∈S,∀d∈S,c≠d→Disjoint
      (B (mixedRestrictedPhysicalLift R e lift c).1 (mixedRestrictedPhysicalLift R e lift c).2)
      (B (mixedRestrictedPhysicalLift R e lift d).1 (mixedRestrictedPhysicalLift R e lift d).2)) ∧
    ((∀c∈S,(restrictedResourceSet (mixedCandidateResources R) e c).Nonempty) →
      Set.InjOn (mixedRestrictedPhysicalLift R e lift) (↑S:Set _)) :=by
  let Btotal: (Σi,W i)→Finset Y:=fun z=>B z.1 z.2
  have hp:∀c∈S,Btotal (mixedRestrictedPhysicalLift R e lift c)=
      (restrictedResourceSet (mixedCandidateResources R) e c).image φ:=by
    intro c _
    exact mixed_restricted_physical_lift_resources R e φ lift B h c
  constructor
  · exact matching_physical_lift S _ φ _ Btotal hφ hmatch hp
  · intro hne
    exact matching_physical_lift_injective_on S _ φ _ Btotal hφ hmatch hp hne
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V X Y:Type} [Fintype I] [Fintype V] [Fintype X] [DecidableEq I]
  [DecidableEq V] [DecidableEq X] [DecidableEq Y]
  {E:I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_positive_matching_physical_realizations
    (R:∀i,E i→Finset V) (e:X↪V) (φ:X→Y) (hφ:Function.Injective φ) {W:I→Type}
    (lift:∀i,RestrictedResource (R i) e→W i) (B:∀i,W i→Finset Y)
    (h:∀i c,B i (lift i c)=(restrictedResourceSet (R i) e c).image φ)
    (w:∀i,E i→ℝ)
    (hsize:∀i c,0<w i c→1≤(R i c).card)
    (S:Finset (RestrictedResource (mixedCandidateResources R) e))
    (hpos:∀c∈S,0<mixedCandidateWeight w c.val)
    (hmatch:∀c∈S,∀d∈S,c≠d→Disjoint
      (restrictedResourceSet (mixedCandidateResources R) e c)
      (restrictedResourceSet (mixedCandidateResources R) e d)):
    (∀c∈S,∀d∈S,c≠d→Disjoint
      (B (mixedRestrictedPhysicalLift R e lift c).1 (mixedRestrictedPhysicalLift R e lift c).2)
      (B (mixedRestrictedPhysicalLift R e lift d).1 (mixedRestrictedPhysicalLift R e lift d).2)) ∧
    Set.InjOn (mixedRestrictedPhysicalLift R e lift) (↑S:Set _) :=by
  obtain ⟨hdis,hinj⟩:=mixed_restricted_matching_physical_realizations R e φ hφ lift B h S hmatch
  refine ⟨hdis,hinj ?_⟩
  intro c hc
  apply Finset.card_pos.mp
  rw [restrictedResourceSet_card]
  exact Nat.lt_of_lt_of_le (by decide : 0<1) (hsize c.val.1 c.val.2 (hpos c hc))
end Oberwolfach
