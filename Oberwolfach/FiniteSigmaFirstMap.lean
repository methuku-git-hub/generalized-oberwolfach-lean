module

public import Oberwolfach.RawRetentionProjection
public import Oberwolfach.FiniteLawMap

@[expose] public section
/-! A dependent second-stage law projects back to its first-stage law. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_sigma_map_first_dependent {Ω:Type} [Fintype Ω]
    {F:Ω→Type} [∀ ω,Fintype (F ω)] (μ:FiniteLaw Ω) (ν:∀ ω,FiniteLaw (F ω)):
    (μ.sigma ν).map Sigma.fst=μ:=by
  apply finiteLaw_ext
  intro x
  have hh:=finiteLaw_sigma_first_probability μ ν (fun y=>y=x)
  have hm:=finiteLaw_map_probability (μ.sigma ν) Sigma.fst (fun y=>y=x)
  have hp:=hm.trans hh
  simpa [FiniteLaw.probability,eq_comm] using hp
end Oberwolfach
