module

public import Oberwolfach.TwoStageEvents

@[expose] public section
/-! A deterministic first stage does not change the second-stage law. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def finiteLawUnit:FiniteLaw Unit :=
  {mass:=fun _=>1,nonneg:=by intro _;norm_num,total:=by simp}

theorem finiteLaw_unit_sigma_probability {Ω:Type} [Fintype Ω] (μ:FiniteLaw Ω) (E:Ω→Prop):
    (finiteLawUnit.sigma (fun _=>μ)).probability (fun z=>E z.2)=μ.probability E :=by
  rw [finiteLaw_sigma_probability]
  simp [FiniteLaw.expectation, finiteLawUnit]
end Oberwolfach
