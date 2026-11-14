module

public import Oberwolfach.LongPreparationUnassignedIdentity

@[expose] public section
/-! The physical unassigned density inherits the upper bound on each
fixed hub residual; it is the prescribed average, not a new sample. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem long_preparation_physical_unassigned_upper {U:Type} [Fintype U]
    (D ρ θ:ℝ) (hD:0<D) (hρ:0≤ρ) (hρhi:ρ≤1) (hθ:0≤θ)
    (hsize:ρ*D=2*Fintype.card U) (residual:U→ℝ)
    (hres:∀w,0≤residual w ∧ residual w≤2*θ):
    0≤2*(∑w,residual w)/D ∧ 2*(∑w,residual w)/D≤2*θ:=by
  have hsum0:0≤∑w,residual w:=Finset.sum_nonneg (fun w _=>(hres w).1)
  have hsum:(∑w,residual w)≤(Fintype.card U:ℝ)*(2*θ):=by
    calc
      (∑w,residual w)≤∑_w:U,(2*θ) := Finset.sum_le_sum (fun w _=>(hres w).2)
      _ = (Fintype.card U:ℝ)*(2*θ) := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  constructor
  · positivity
  · apply (div_le_iff₀ hD).mpr
    have hρθ:ρ*(2*θ)≤2*θ:=by
      nlinarith [mul_nonneg hθ (sub_nonneg.mpr hρhi)]
    have hnum:2*(∑w,residual w)≤ρ*D*(2*θ):=by nlinarith [hsum,hsize]
    have hh:=mul_le_mul_of_nonneg_right hρθ hD.le
    nlinarith
end Oberwolfach
