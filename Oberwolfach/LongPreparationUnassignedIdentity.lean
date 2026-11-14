module

public import Oberwolfach.LongPreparationPhysicalFeasible

@[expose] public section
/-! The unassigned-state probability is exactly the density times the
average residual marginal, with no resampling. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_preparation_unassigned_probability {U:Type} [Fintype U]
    (D ρ s t:ℝ) (hD:0<D) (hU:0<Fintype.card U)
    (a b:U→ℝ) (hsize:ρ*D=2*Fintype.card U):
    ρ*((∑ v,(1-s-t-a v-b v))/(Fintype.card U:ℝ))=
      2*(∑ v,(1-s-t-a v-b v))/D:=by
  have hcard:(0:ℝ)<Fintype.card U:=by exact_mod_cast hU
  field_simp
  have hh:=congrArg (fun x:ℝ=>x*(∑ v,(1-s-t-a v-b v))) hsize
  nlinarith [hh]
end Oberwolfach
