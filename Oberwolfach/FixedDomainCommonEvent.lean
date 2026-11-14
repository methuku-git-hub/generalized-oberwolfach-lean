module

public import Oberwolfach.ConfigurationFailureMargins
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Union bounds for fixed domains whose sizes are comparable with the
ambient order. The local failure exponent is increased before any domains
or events are selected. No independence between their events is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem fixed_domain_common_event (κ:ℝ) (hκ:0<κ) (q:ℕ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→∀ (Ω J:Type) [Fintype Ω] [Fintype J],Fintype.card J≤n→
      ∀ (μ:FiniteLaw Ω) (s:J→ℕ) (A:J→Ω→Prop),
      (∀ j,κ*n≤(s j:ℝ))→
      (∀ j,1-1/(s j:ℝ)^(q+2)≤μ.probability (A j))→
      1-1/(n:ℝ)^q≤μ.probability (fun ω=>∀ j,A j ω):=by
  obtain ⟨N,hN⟩:=exists_nat_ge (1/κ^(q+2))
  refine ⟨max N 1,?_⟩
  intro n hn Ω J _ _ hJ μ s A hs hA
  have hn0:0<n:=by omega
  have hnR:(0:ℝ)<n:=Nat.cast_pos.mpr hn0
  have hκn:0<κ*n:=mul_pos hκ hnR
  have hbad (j:J):μ.probability (fun ω=>¬A j ω)≤1/(κ*n)^(q+2):=by
    have hcomp:=finiteLaw_probability_compl μ (A j)
    have hlocal:μ.probability (fun ω=>¬A j ω)≤1/(s j:ℝ)^(q+2):=by linarith only [hcomp,hA j]
    exact hlocal.trans (div_le_div_of_nonneg_left (by norm_num) (pow_pos hκn _)
      (pow_le_pow_left₀ hκn.le (hs j) _))
  have hevent:=finiteLaw_common_event_lower μ Finset.univ (fun j ω=>¬A j ω)
    (fun _=>1/(κ*n)^(q+2)) (fun j _=>hbad j)
  simp only [not_not,Finset.mem_univ,true_implies,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hevent
  have hsize:(Fintype.card J:ℝ)*(1/(κ*n)^(q+2))≤(n:ℝ)*(1/(κ*n)^(q+2)):=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hJ) (by positivity)
  have he:(n:ℝ)*(1/(κ*n)^(q+2))=(1/κ^(q+2))/(n:ℝ)^(q+1):=by
    rw [mul_pow,show q+2=(q+1)+1 by omega,pow_succ (n:ℝ)]
    field_simp
  have hC:1/κ^(q+2)≤(n:ℝ):=hN.trans (by exact_mod_cast (show N≤n by omega))
  have hsmall:=hsize.trans (he.trans_le (scaled_inverse_power_le n q hn0 _ hC))
  exact (sub_le_sub_left hsmall 1).trans hevent

end Oberwolfach
