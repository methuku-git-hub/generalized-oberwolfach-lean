module

public import Oberwolfach.PreparationClassFailureBudget

@[expose] public section
/-! The polynomial reservoir losses can be absorbed into the arbitrary
failure allowance while retaining the original n⁻¹⁰ term. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_combined_loss_power_ten_eventually (χ:ℝ) (hχ:0<χ):
    ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀loss:ℝ,loss≤χ/2→
      loss+2/(n:ℝ)^10+(1/(n:ℝ)+2/(n:ℝ)^2)≤χ+1/(n:ℝ)^10 :=by
  obtain ⟨N₀,hN₀⟩:=exists_nat_gt (8/χ)
  refine ⟨max 1 N₀,by omega,?_⟩
  intro n hn loss hloss
  have hn0:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hn1:(1:ℝ)≤n:=by exact_mod_cast (show 1≤n by omega)
  have hnN:(N₀:ℝ)≤n:=by exact_mod_cast (show N₀≤n by omega)
  have hinv:(1:ℝ)/n<χ/8:=by
    have hh:(8/χ:ℝ)<n:=hN₀.trans_le hnN
    apply (div_lt_iff₀ hn0).2
    have hh':(8:ℝ)<(n:ℝ)*χ:=(div_lt_iff₀ hχ).1 hh
    nlinarith
  have hpow1:1≤(n:ℝ)^9:=one_le_pow₀ hn1
  have hpow:(n:ℝ)≤(n:ℝ)^10:=by rw [pow_succ];nlinarith
  have hten:(1:ℝ)/(n:ℝ)^10≤1/n:=one_div_le_one_div_of_le hn0 hpow
  have hsq:(1:ℝ)/(n:ℝ)^2≤1/n:=by
    apply one_div_le_one_div_of_le hn0
    nlinarith
  have hten2:2/(n:ℝ)^10=2*((1:ℝ)/(n:ℝ)^10):=by ring
  have hsq2:2/(n:ℝ)^2=2*((1:ℝ)/(n:ℝ)^2):=by ring
  rw [hten2,hsq2]
  linarith
end Oberwolfach
