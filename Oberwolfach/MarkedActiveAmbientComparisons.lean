module

public import Oberwolfach.MarkedReferenceActiveMinimumAllTypes

@[expose] public section
/-! Pure arithmetic for the ambient-size hypotheses of the fixed-domain
sampling event. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_ambient_comparisons
    (n u a b iota omega:ℝ) (hiota:0 < iota) (homega:0 < omega)
    (ha:0≤a) (hb:0≤b) (hu:u≤n) (hI:iota*n≤a) (hJ:omega*a≤b):
    let K:=1+1/iota+1/(iota*omega)
    1≤K ∧ n≤K*a ∧ u≤K*a ∧ n≤K*b:=by
  intro K
  have hnI:n≤(1/iota)*a:=by
    rw [one_div,mul_comm]
    apply (le_div_iff₀ hiota).2
    simpa only [mul_comm] using hI
  have hnJ:n≤(1/(iota*omega))*b:=by
    have hprod:0 < iota*omega:=mul_pos hiota homega
    rw [one_div,mul_comm]
    apply (le_div_iff₀ hprod).2
    have hm:=mul_le_mul_of_nonneg_left hI (le_of_lt homega)
    nlinarith [hJ]
  have h1:0≤(1/iota:ℝ):=by positivity
  have h2:0≤(1/(iota*omega):ℝ):=by positivity
  have hK:1≤K:=by dsimp [K];linarith
  have hK1:(1/iota:ℝ)≤K:=by dsimp [K];linarith
  have hK2:(1/(iota*omega):ℝ)≤K:=by dsimp [K];linarith
  have hnI':n≤K*a:=hnI.trans (mul_le_mul_of_nonneg_right hK1 ha)
  exact ⟨hK,hnI',hu.trans hnI',hnJ.trans (mul_le_mul_of_nonneg_right hK2 hb)⟩
end Oberwolfach
