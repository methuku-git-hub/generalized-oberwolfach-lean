module

public import Oberwolfach.OrdinaryInducedPotentialFailure

@[expose] public section
/-! The raw-parent, reference/rim, cover, reservoir and adaptive-potential
    failures can be made jointly small on comparably sized domains. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
noncomputable section
namespace Oberwolfach

theorem ordinary_combined_failure_eventually_small
    (K B t ε : ℝ) (d : ℕ) (hK : 0≤K) (hB : 0<B) (ht : 0<t) (hε : 0<ε) :
    ∃ N : ℕ, ∀ n m u : ℕ, N≤n → N≤m → (u:ℝ)≤K*m →
      (1/(n:ℝ)+3/(n:ℝ)^2)+3/(m:ℝ)+1/(n:ℝ)+1/(m:ℝ)+
      1/(n:ℝ)+(1/(n:ℝ)+2/(n:ℝ)^2)+
      (m:ℝ)*u*(2*Real.exp (-2*t^2 /
        ((4*(d:ℝ)+3)^2*((3:ℝ)^4*B/m)*(2*3)*((3:ℝ)^2*B)))) < ε := by
  obtain ⟨Nexp,hNexp⟩:=ordinary_induced_potential_failure_eventually_small K B t (ε/2) d hK hB ht (by positivity)
  obtain ⟨Ninv,hNinv⟩:=exists_nat_gt (26/ε)
  refine ⟨max 1 (max Nexp Ninv),?_⟩
  intro n m u hn hm hu
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hm0 : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hnN : (Ninv:ℝ)≤n := by exact_mod_cast (show Ninv≤n by omega)
  have hmN : (Ninv:ℝ)≤m := by exact_mod_cast (show Ninv≤m by omega)
  have hni : (1:ℝ)/n<ε/26 := by
    have hh : (26/ε:ℝ)<n := hNinv.trans_le hnN
    apply (div_lt_iff₀ hn0).2
    have ht' := (div_lt_iff₀ hε).1 hh
    nlinarith
  have hmi : (1:ℝ)/m<ε/26 := by
    have hh : (26/ε:ℝ)<m := hNinv.trans_le hmN
    apply (div_lt_iff₀ hm0).2
    have ht' := (div_lt_iff₀ hε).1 hh
    nlinarith
  have hsq : (1:ℝ)/(n:ℝ)^2≤1/n := by
    apply one_div_le_one_div_of_le hn0
    nlinarith
  have h3 : (3:ℝ)/(n:ℝ)^2≤3*(1/n) := by
    have hh:=mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤3 by norm_num)
    simpa only [div_eq_mul_inv,one_mul] using hh
  have h2 : (2:ℝ)/(n:ℝ)^2≤2*(1/n) := by
    have hh:=mul_le_mul_of_nonneg_left hsq (show (0:ℝ)≤2 by norm_num)
    simpa only [div_eq_mul_inv,one_mul] using hh
  have h3m : (3:ℝ)/m=3*(1/m) := by ring
  have hexp:=hNexp m u (by omega) hu
  rw [h3m]
  linarith
end Oberwolfach
