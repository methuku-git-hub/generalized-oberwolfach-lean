module

public import Oberwolfach.LongPreparationDensityBounds

@[expose] public section
/-! The retained component fractions define the original hub coefficients.
The balance and coefficient bounds are consequences of those definitions. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_coefficient_balance {U I:Type} [Fintype U] [Fintype I]
    (D m θ:ℝ) (hD:0<D) (hm:0≤m) (hθ:θ≤1)
    (a b:U→ℝ) (f:I→U→ℝ)
    (ha:∀ u,0≤a u) (hb:∀ u,0<b u ∧ b u≤1) (hf:∀ i u,0≤f i u)
    (hdefinition:∀ u,b u=m*a u+(1-θ)*∑ i,f i u):
    let η:=fun i u=>(1-θ)*f i u/b u
    let p:=(∑ u,b u)/D
    let k:=(∑ u,a u)/D;
    (∀ i u,0≤η i u ∧ η i u≤1/b u) ∧
    (∀ u,m*a u+(∑ i,η i u)*b u=b u) ∧
    (∑ u,a u)=D*k ∧ (∑ u,b u)=D*p:=by
  intro η p k
  have hfactor:0≤1-θ:=by linarith
  have htotal (u:U):(∑ i,η i u)*b u=(1-θ)*∑ i,f i u:=by
    dsimp [η]
    rw [← Finset.sum_div,← Finset.mul_sum]
    field_simp [(hb u).1.ne']
  have hindividual (i:I) (u:U):(1-θ)*f i u≤b u:=by
    have hfi:f i u≤∑ i,f i u:=Finset.single_le_sum (fun i _=>hf i u) (Finset.mem_univ i)
    have h1:=mul_le_mul_of_nonneg_left hfi hfactor
    have hma:=mul_nonneg hm (ha u)
    linarith [hdefinition u]
  refine ⟨?_,?_,?_,?_⟩
  · intro i u
    constructor
    · dsimp [η]
      exact div_nonneg (mul_nonneg hfactor (hf i u)) (hb u).1.le
    · dsimp [η]
      apply (div_le_div_iff_of_pos_right (hb u).1).2
      exact (hindividual i u).trans (hb u).2
  · intro u
    rw [htotal u]
    exact (hdefinition u).symm
  · dsimp [k]
    field_simp
  · dsimp [p]
    field_simp
end Oberwolfach
