module

public import Oberwolfach.MarkedReferenceParentBase

@[expose] public section
/-! Exact substitutions for the reference event in the level-record fields. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_reference_parameter_normalization (r:ℕ) (α ρ s₀:ℝ) :
    let c:ℝ:=r+4
    let t:=s₀/c
    let p:=ρ*s₀/2
    let gamma:=α/16
    c*t=s₀ ∧ ρ*c*t/2=p ∧ p/c=(ρ*c*t/2)/c ∧ 2*gamma=(α/2)/4:=by
  intro c t p gamma
  have hc:0<c:=by dsimp [c];positivity
  dsimp [t,p,gamma]
  field_simp
  <;> simp_all <;> ring

theorem marked_reference_parent_minimum_degree_comparison
    (α n degree:ℝ) (hα:0≤α) (hn:0≤n)
    (hdegree:(1/2+α/2)*n≤degree):
    (1/2+(α/16)/2)*n≤degree:=by
  have hh:=mul_le_mul_of_nonneg_right (show (1/2+(α/16)/2:ℝ)≤1/2+α/2 by linarith) hn
  exact hh.trans hdegree
end Oberwolfach
