module

public import Oberwolfach.OrdinaryMixedGenericFamily

@[expose] public section
/-! Recover the marked wheel from a mixed candidate tagged by `none`. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

def ordinaryMixedNonePayload {I CM:Type} {CO:I→Type}
    (x:{c:Σj,OrdinaryMixedGenericFamily CM CO j // c.1.isNone}):CM :=by
  rcases x with ⟨⟨j,w⟩,hj⟩
  cases j with
  | none => exact w
  | some i => simp at hj

theorem ordinary_mixed_none_payload_original {I CM:Type} {CO:I→Type}
    (x:{c:Σj,OrdinaryMixedGenericFamily CM CO j // c.1.isNone}):
    x.val=⟨none,ordinaryMixedNonePayload x⟩ :=by
  rcases x with ⟨⟨j,w⟩,hj⟩
  cases j with
  | none => rfl
  | some i => simp at hj
end Oberwolfach
