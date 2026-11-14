module

public import Oberwolfach.RawOrdinarySeedPhysicalResources
public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber
public import Oberwolfach.WheelRunPhysicalEdgeSaturation

@[expose] public section
/-! Translate the matching's Sym2 resources to the finite-set resources used
by the buffered wheel-packing lemmas, injectively. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]

def ordinaryPhysicalResourceToFinite:Sym2 V⊕(V×U)→Finset V⊕(V×U):=
  Sum.map Sym2.toFinset id

theorem ordinary_physical_resource_to_finite_injective:
    Function.Injective (ordinaryPhysicalResourceToFinite (V:=V) (U:=U)):=by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      exact sym2_toFinset_injective_local (Sum.inl.inj hab)
    | inr b => cases hab
  | inr a =>
    cases b with
    | inl b => cases hab
    | inr b =>
      apply congrArg Sum.inr
      exact Sum.inr.inj hab

theorem ordinary_physical_resource_to_finite_comp (π:Equiv.Perm V):
    ordinaryPhysicalResourceToFinite ∘ ordinaryMixedPhysicalResource (U:=U) π = markedSeedPhysicalMap π :=by
  funext x
  cases x with
  | inl e =>
    cases e <;> simp [ordinaryPhysicalResourceToFinite,ordinaryMixedPhysicalResource,markedPairPhysical,
      markedSeedPhysicalMap,physicalResourceToFinite,typedResourcePhysical,markedResourceTypeEquiv,Sym2.toFinset_mk_eq]
  | inr p =>
    rcases p with ⟨j,v,u⟩
    rfl
end Oberwolfach
