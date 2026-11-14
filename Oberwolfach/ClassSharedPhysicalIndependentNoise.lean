module

public import Oberwolfach.FiniteProductBothMaps
public import Oberwolfach.FiniteProductProjection

@[expose] public section
/-! Independent class-local interval experiments may be attached to the
shared physical experiment without changing any class's product marginal. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_pi_map_coordinate {I:Type} [Fintype I] [DecidableEq I]
    {A:I→Type} [∀ i,Fintype (A i)] (ν:∀ i,FiniteLaw (A i)) (i:I):
    (FiniteLaw.pi ν).map (fun z=>z i)=ν i:=by
  apply finiteLaw_ext
  intro x
  have hh:=finiteLaw_pi_coordinate_probability ν i x
  have hm:=finiteLaw_map_probability (FiniteLaw.pi ν) (fun z=>z i) (fun y=>y=x)
  have hp:=hm.trans hh
  simpa [FiniteLaw.probability,eq_comm] using hp

theorem class_shared_physical_independent_noise {I Ω:Type} [Fintype I] [DecidableEq I] [Fintype Ω]
    {A B:I→Type} [∀ i,Fintype (A i)] [∀ i,Fintype (B i)]
    (μ:FiniteLaw Ω) (view:∀ i,Ω→A i) (noise:∀ i,FiniteLaw (B i)):
    ∀ i,(μ.prod (FiniteLaw.pi noise)).map (fun z=>(view i z.1,z.2 i))=
      (μ.map (view i)).prod (noise i):=by
  intro i
  rw [finiteLaw_prod_map_both μ (FiniteLaw.pi noise) (view i) (fun z=>z i),finiteLaw_pi_map_coordinate]
end Oberwolfach
