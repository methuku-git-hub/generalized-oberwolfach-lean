module

public import Oberwolfach.OrdinaryMixedGenericFamily

@[expose] public section
/-! Extract the ordinary tuple and its index from a mixed candidate whose
option tag is known to be present. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ordinaryMixedSomePayload {I CM:Type} {CO:I→Type}
    (x:{c:Σj,OrdinaryMixedGenericFamily CM CO j // c.1.isSome}):Σi,CO i :=by
  rcases x with ⟨⟨j,w⟩,hj⟩
  cases j with
  | none => simp at hj
  | some i => exact ⟨i,w⟩

theorem ordinary_mixed_some_payload_original {I CM:Type} {CO:I→Type}
    (x:{c:Σj,OrdinaryMixedGenericFamily CM CO j // c.1.isSome}):
    x.val=⟨some (ordinaryMixedSomePayload x).1,(ordinaryMixedSomePayload x).2⟩ :=by
  rcases x with ⟨⟨j,w⟩,hj⟩
  cases j with
  | none => simp at hj
  | some i => rfl
end Oberwolfach
