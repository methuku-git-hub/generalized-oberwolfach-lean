module

public import Oberwolfach.VortexStepMargins

@[expose] public section
/-! Uniform fixed-size vortex steps allow any fixed linear number of roots. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem eventually_vortex_step_margins_root_ratio {ε C:ℝ} (he:0<ε) (hC:0<C):
    ∃N:ℕ,∀n:ℕ,N≤n→2≤n ∧ 2≤ε*n ∧
      (2*C*(n:ℝ))*Real.exp (-ε*(n:ℝ)^(1/3:ℝ))<1 :=by
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (2*C) 1 (c:=ε) (p:=1/3) he (by norm_num) 1
  refine ⟨max 2 (max N (Nat.ceil (2/ε))),?_⟩
  intro n hn
  have hn2:2≤n:=by omega
  have hnreal:(1:ℝ)<n:=by exact_mod_cast (show 1<n by omega)
  have hceil:(Nat.ceil (2/ε):ℝ)≤n:=by exact_mod_cast (show Nat.ceil (2/ε)≤n by omega)
  have he2:2≤ε*n:=by
    have hh:=(Nat.le_ceil (2/ε)).trans hceil
    have hh':=(div_le_iff₀ he).mp hh
    nlinarith
  refine ⟨hn2,he2,?_⟩
  have hh:=hN n (by omega)
  simp only [Real.rpow_one,pow_one] at hh
  exact hh.trans_lt ((div_lt_one (by linarith:(0:ℝ)<n)).mpr hnreal)
end Oberwolfach
