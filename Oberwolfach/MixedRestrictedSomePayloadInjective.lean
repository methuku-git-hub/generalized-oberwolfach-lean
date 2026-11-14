module

public import Oberwolfach.MixedRestrictedSomePayload

@[expose] public section
/-! Distinct selected mixed candidates have distinct extracted ordinary
components, so multiplicities are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V W:Type} [Fintype I] [Fintype V] [Fintype W] [DecidableEq I]
  [DecidableEq V] [DecidableEq W] {E:Option I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

theorem mixed_restricted_some_payload_injective (R:∀i,E i→Finset V) (e:W↪V):
    Function.Injective (mixedRestrictedSomePayload R e) :=by
  intro c d h
  apply Subtype.ext
  apply (mixedRestrictedFamilyEquiv R e).injective
  have h': (⟨mixedRestrictedFamilyEquiv R e c.val,by simpa [mixedRestrictedFamilyEquiv] using c.property⟩ :
      {z:Σi,RestrictedResource (R i) e // z.1.isSome}) =
      ⟨mixedRestrictedFamilyEquiv R e d.val,by simpa [mixedRestrictedFamilyEquiv] using d.property⟩:=
    option_some_sigma_payload_injective h
  exact congrArg Subtype.val h'
end Oberwolfach
