module

public import Oberwolfach.OptionSomeSigmaPayload
public import Oberwolfach.MixedRestrictedPhysicalLift

@[expose] public section
/-! Extract an ordinary component from an actually restricted mixed
candidate, preserving its index and exact restricted resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V W:Type} [Fintype I] [Fintype V] [Fintype W] [DecidableEq I]
  [DecidableEq V] [DecidableEq W] {E:Option I→Type} [∀i,Fintype (E i)] [∀i,DecidableEq (E i)]

def mixedRestrictedSomePayload (R:∀i,E i→Finset V) (e:W↪V)
    (c:{c:RestrictedResource (mixedCandidateResources R) e // c.val.1.isSome}):
    Σi,RestrictedResource (R (some i)) e :=
  optionSomeSigmaPayload ⟨mixedRestrictedFamilyEquiv R e c.val,by simpa [mixedRestrictedFamilyEquiv] using c.property⟩

theorem mixed_restricted_some_payload_index (R:∀i,E i→Finset V) (e:W↪V)
    (c:{c:RestrictedResource (mixedCandidateResources R) e // c.val.1.isSome}):
    some (mixedRestrictedSomePayload R e c).1=c.val.val.1:=by
  exact option_some_sigma_payload_index _

theorem mixed_restricted_some_payload_resources (R:∀i,E i→Finset V) (e:W↪V)
    (c:{c:RestrictedResource (mixedCandidateResources R) e // c.val.1.isSome}):
    restrictedResourceSet (R (some (mixedRestrictedSomePayload R e c).1)) e
      (mixedRestrictedSomePayload R e c).2 =
        restrictedResourceSet (mixedCandidateResources R) e c.val :=by
  rcases c with ⟨⟨⟨i,v⟩,hv⟩,hi⟩
  cases i with
  | none => simp at hi
  | some i => rfl
end Oberwolfach
