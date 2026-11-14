module

public import Oberwolfach.RestrictedResourceNestedLift
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! Lifting a matching from the surviving resource set preserves its physical
rim union exactly. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem physical_rim_candidate_union_nested_lift
    {V W₁ W₂ C X U:Type} [Fintype V] [DecidableEq V] [Fintype W₁] [DecidableEq W₁]
    [Fintype W₂] [DecidableEq W₂] [Fintype C] [DecidableEq C] [Fintype X] [DecidableEq X] [Fintype U] [DecidableEq U]
    (R:C→Finset V) (e₁:W₁↪V) (e₂:W₂↪V) (f:W₁↪W₂)
    (hf:∀w,e₂ (f w)=e₁ w) (φ:W₂↪Sym2 X⊕(X×U))
    (M:Finset (RestrictedResource R e₁)):
    physicalRimCandidateUnion (f.trans φ) (restrictedResourceSet R e₁) M =
      physicalRimCandidateUnion φ (restrictedResourceSet R e₂)
        (M.map (restrictedResourceNestedLift R e₁ e₂ f hf)):=by
  ext x y
  constructor
  · rintro ⟨hxy,c,hc,w,hw,he⟩
    refine ⟨hxy,restrictedResourceNestedLift R e₁ e₂ f hf c,Finset.mem_map.mpr ⟨c,hc,rfl⟩,f w,?_,he⟩
    rw [restricted_resource_nested_lift_set]
    exact Finset.mem_map.mpr ⟨w,hw,rfl⟩
  · rintro ⟨hxy,c,hc,w,hw,he⟩
    obtain ⟨c',hc',rfl⟩:=Finset.mem_map.mp hc
    rw [restricted_resource_nested_lift_set] at hw
    obtain ⟨w',hw',rfl⟩:=Finset.mem_map.mp hw
    exact ⟨hxy,c',hc',w',hw',he⟩
end Oberwolfach
