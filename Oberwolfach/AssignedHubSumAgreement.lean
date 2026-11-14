module

public import Oberwolfach.LongRawPartialDomainCard

@[expose] public section
/-! Reindex a sum by either of two provably equal hub assignments. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem assigned_hub_sum_agreement
    {A U:Type} [Fintype A] [DecidableEq A] [DecidableEq U]
    (hub₁ hub₂:A→U) (h:∀a,hub₁ a=hub₂ a) (w:U) (weight:A→ℕ):
    ∑a:{a:A // hub₁ a=w},weight a.val = ∑a:{a:A // hub₂ a=w},weight a.val:=by
  let e:{a:A // hub₁ a=w}≃{a:A // hub₂ a=w}:=
    { toFun:=fun a=>⟨a.val,(h a.val).symm.trans a.property⟩
      invFun:=fun a=>⟨a.val,(h a.val).trans a.property⟩
      left_inv:=by intro a;cases a;rfl
      right_inv:=by intro a;cases a;rfl }
  apply Fintype.sum_equiv e
  intro a
  rfl
end Oberwolfach
