module

public import Oberwolfach.MixedRestrictedFamilyEquiv

@[expose] public section
/-! Split the ordinary part of any option-indexed dependent family without
changing either its index or its payload. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {I:Type} {E:Option I→Type}

def optionSomeSigmaPayload (z:{z:Σi,E i // z.1.isSome}):Σi,E (some i):=by
  rcases z with ⟨⟨i,c⟩,hi⟩
  cases i with
  | none => simp at hi
  | some i => exact ⟨i,c⟩

theorem option_some_sigma_payload_index (z:{z:Σi,E i // z.1.isSome}):
    some (optionSomeSigmaPayload z).1=z.val.1:=by
  rcases z with ⟨⟨i,c⟩,hi⟩
  cases i with
  | none => simp at hi
  | some i => rfl

theorem option_some_sigma_payload_injective:
    Function.Injective (optionSomeSigmaPayload (E:=E)):=by
  rintro ⟨⟨i,c⟩,hi⟩ ⟨⟨j,d⟩,hj⟩ h
  cases i with
  | none => simp at hi
  | some i =>
    cases j with
    | none => simp at hj
    | some j =>
      change (⟨i,c⟩:Σi,E (some i))=⟨j,d⟩ at h
      cases h
      rfl
end Oberwolfach
