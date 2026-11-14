module

public import Oberwolfach.LongPreparationResidualBounds

@[expose] public section
/-! The unassigned marginal is exactly the part left by the omitted short
components, not an independently chosen density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_preparation_residual_identity
    (c θ ℓ f rare s:ℝ) (hc:1<c) (hfractions:ℓ+f+rare=1):
    let t:=s/(c-1)
    let a:=(1-θ)*ℓ/c-t
    let b:=(c-1)*a+(1-θ)*f;
    1-s-t-a-b=θ+(1-θ)*rare:=by
  intro t a b
  have hc0:0<c:=by linarith
  have hcm:0<c-1:=by linarith
  have ht:(c-1)*t=s:=by dsimp [t];field_simp
  have ha:c*(a+t)=(1-θ)*ℓ:=by dsimp [a];field_simp;ring
  have hf:(1-θ)*(ℓ+f+rare)=1-θ:=by rw [hfractions];ring
  dsimp [b]
  nlinarith [ht,ha,hf]
end Oberwolfach
