module

public import Oberwolfach.FiniteProductBothMaps

@[expose] public section
/-! Swapping independent coordinates swaps their product laws. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_prod_swap {A B:Type} [Fintype A] [Fintype B]
    (μ:FiniteLaw A) (ν:FiniteLaw B):
    (μ.prod ν).map Prod.swap=ν.prod μ:=by
  apply finiteLaw_ext
  rintro ⟨b,a⟩
  simp only [FiniteLaw.map,FiniteLaw.prod,Fintype.sum_prod_type,Prod.swap,Prod.mk.injEq]
  have heach (x:A):(∑ y:B,if y=b ∧ x=a then μ.mass x*ν.mass y else 0)=
      if x=a then μ.mass x*ν.mass b else 0:=by
    by_cases h:x=a <;> simp [h]
  calc
    _ = ∑ x:A,if x=a then μ.mass x*ν.mass b else 0:=by
      apply Finset.sum_congr rfl
      intro x _
      convert heach x using 1
    _ = _:=by simp [mul_comm]
end Oberwolfach
