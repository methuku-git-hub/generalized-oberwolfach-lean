module

public import Mathlib.Tactic

@[expose] public section
/-! The full-parent to inner-domain ratio is at most a constant times
    1/ε, so the explicit cleanup margins lose only one factor of ε. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_vortex_domain_margin_linear
    (ε ρ₀ c:ℝ) (hε:0<ε) (hε1:ε≤1) (hρ:0<ρ₀) (hc:0<c):
    let K:ℝ:=2*(1+1/(ε/2)+1/((ε/2)*(ρ₀/8)))
    let C:ℝ:=6+32/ρ₀;
    0<K ∧ 0<C ∧ (c/(4*C))*ε≤c/(4*K) :=by
  intro K C
  have hK:0<K:=by dsimp [K];positivity
  have hC:0<C:=by dsimp [C];positivity
  have hKeq:K*ε=2*ε+4+32/ρ₀:=by
    dsimp [K]
    field_simp
    <;> ring
  have hKbound:K*ε≤C:=by dsimp [C];rw [hKeq];linarith
  have hcoeff:0≤c/(4*C):=by positivity
  have hmul:=mul_le_mul_of_nonneg_left hKbound hcoeff
  have heq:(c/(4*C))*C*4=c:=by field_simp <;> ring
  refine ⟨hK,hC,?_⟩
  apply (le_div_iff₀ (by positivity : 0<4*K)).2
  nlinarith only [hmul,heq]
end Oberwolfach
